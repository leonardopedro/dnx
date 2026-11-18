//! Export a dnx DeltaNet into the kernel's (`unfer/logos`) net representation.
//!
//! The two implementations encode the same calculus differently:
//!
//! | concept | dnx | unfer |
//! |---|---|---|
//! | abstraction | `FAN_ABS` (`aux0`=body, `aux1`=var) | `Abs` (slot 1=var, slot 2=body) |
//! | application | `FAN_APP` (`principal`=fn, `aux0`=result, `aux1`=arg) | `App` (slot 1=arg, slot 2=result) |
//! | sharing | `REP_*` (level+deltas) | `Dup(level)` |
//! | eraser | `PortId::ERA` sentinel | `Era` node |
//! | scalar | `PRIM_VAL` + `PrimState` | `Lit` |
//!
//! Only the shared, fully reduced fragment is convertible. Anything whose
//! meaning has no faithful unfer encoding (open terms, unresolvable primitive
//! functions, strings/lists/attrsets, replicator direction) is refused with
//! [`ConvertError::Unsupported`] rather than approximated — a comparison over
//! a guessed encoding would report a false verdict.

use dnx_core::prim::{PrimState, PrimValue};
use dnx_core::{Canonical, Net, PortId, PortKind, SlotView, ΔK};
use logos::core_ir::Literal;
use logos::deltanet::{AgentKind, Net as KernelNet, Port as KernelPort};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvertError {
    /// The net uses a construct with no faithful kernel encoding.
    Unsupported(String),
    /// The net is malformed (a live port with no target, an unwired value).
    Malformed(String),
}

impl std::fmt::Display for ConvertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConvertError::Unsupported(m) => write!(f, "unsupported fragment: {m}"),
            ConvertError::Malformed(m) => write!(f, "malformed net: {m}"),
        }
    }
}

impl std::error::Error for ConvertError {}

/// Convert the reduced dnx net reachable from `root` into a kernel `Net`.
///
/// The result carries no `active_pairs` (they are irrelevant to canonical
/// serialization) and no `var_bindings`; what matters is the node graph and
/// `root`, which is what `unf_hash` walks.
pub fn to_kernel_net(
    net: &Net<Canonical, ΔK>,
    prim: &PrimState,
    root: PortId,
) -> Result<KernelNet, ConvertError> {
    let mut builder = Builder {
        src: net,
        prim,
        out: KernelNet::new(),
        nodes: HashMap::new(),
        kinds: HashMap::new(),
        root_idx: root.slot_idx(),
        root_is_free: net
            .slot_view_at(root.slot_idx())
            .map(SlotView::is_free)
            .unwrap_or(false),
    };
    let root_out = builder.emit_port(root)?;
    builder.out.root = root_out;
    Ok(builder.out)
}

struct Builder<'a> {
    src: &'a Net<Canonical, ΔK>,
    prim: &'a PrimState,
    out: KernelNet,
    /// dnx slot index -> kernel node id.
    nodes: HashMap<u32, u32>,
    /// dnx slot index -> the kind the kernel node was created with.
    kinds: HashMap<u32, AgentKind>,
    root_idx: u32,
    root_is_free: bool,
}

impl Builder<'_> {
    fn emit_port(&mut self, p: PortId) -> Result<KernelPort, ConvertError> {
        if p.is_null() {
            return Err(ConvertError::Malformed("unconnected port".into()));
        }
        if p.is_eraser() {
            let node = self.out.alloc_node(AgentKind::Era);
            return Ok(KernelPort::principal(node));
        }
        let idx = p.slot_idx();
        let view = self
            .src
            .slot_view_at(idx)
            .ok_or_else(|| ConvertError::Malformed(format!("port into retired slot {idx}")))?;

        if view.is_free() {
            // A dnx free slot is a wire endpoint. The named root is elided (the
            // kernel root points at the value); any other free slot is an open
            // variable, which has no term-level kernel encoding here.
            if !self.root_is_free || idx != self.root_idx {
                return Err(ConvertError::Unsupported(format!(
                    "open term: free variable v{}",
                    view.free_var_id()
                )));
            }
            let next = PortId::from_raw(view.principal);
            if next.is_null() {
                return Err(ConvertError::Malformed(
                    "root free slot has no target".into(),
                ));
            }
            return self.emit_port(next);
        }

        let node = self.node_for(idx, view)?;
        let kind = self.kinds.get(&idx).ok_or_else(|| {
            ConvertError::Malformed(format!("internal: node {idx} has no recorded kind"))
        })?;
        let slot = kernel_slot(kind, p.port_kind()).ok_or_else(|| {
            ConvertError::Malformed(format!(
                "{} has no {:?} port",
                kind_name(kind),
                p.port_kind()
            ))
        })?;
        Ok(KernelPort::new(node, slot))
    }

    fn node_for(&mut self, idx: u32, view: SlotView) -> Result<u32, ConvertError> {
        if let Some(node) = self.nodes.get(&idx) {
            return Ok(*node);
        }
        let kind = self.kind_of(view)?;
        let node = self.out.alloc_node(kind.clone());
        self.nodes.insert(idx, node);
        self.kinds.insert(idx, kind.clone());

        for (pk, raw) in [
            (PortKind::Principal, view.principal),
            (PortKind::Aux0, view.aux0),
            (PortKind::Aux1, view.aux1),
        ] {
            let Some(slot) = kernel_slot(&kind, pk) else {
                continue;
            };
            if raw == 0 {
                continue;
            }
            let peer = self.emit_port(PortId::from_raw(raw))?;
            self.out.wire(KernelPort::new(node, slot), peer);
        }
        Ok(node)
    }

    fn kind_of(&self, view: SlotView) -> Result<AgentKind, ConvertError> {
        if view.is_fan() {
            return Ok(if view.fan_is_abs() {
                AgentKind::Abs
            } else {
                AgentKind::App
            });
        }
        if view.is_rep() {
            // `Dup` in the kernel carries only a level. A rep-out copy or a
            // partially erased rep has no kernel spelling, and silently
            // collapsing it to `Dup` would equate distinct nets.
            if !view.rep_is_in() {
                return Err(ConvertError::Unsupported(
                    "replicator direction (rep-out copy)".into(),
                ));
            }
            if view.rep_aux0_erased() || view.rep_aux1_erased() {
                return Err(ConvertError::Unsupported(
                    "partially erased replicator".into(),
                ));
            }
            return Ok(AgentKind::Dup(view.data));
        }
        if view.is_prim_val() {
            let value = self.prim.vals.get(view.data as usize).ok_or_else(|| {
                ConvertError::Malformed(format!("prim value {} is not in PrimState", view.data))
            })?;
            return match value {
                PrimValue::Int(n) => Ok(AgentKind::Lit(Literal::Int64(*n))),
                PrimValue::Float(x) => Ok(AgentKind::Lit(Literal::F64(*x))),
                PrimValue::Bool(b) => Ok(AgentKind::Lit(Literal::Bool(*b))),
                other => Err(ConvertError::Unsupported(format!(
                    "{} has no DeltaNet literal ({other:?})",
                    prim_value_kind(other)
                ))),
            };
        }
        if view.is_prim_fun() {
            // A live primitive function means the net is not fully reduced, or
            // the value is a function. The kernel's numeric subset has no
            // general primitive closure, so refusing beats guessing an op.
            return Err(ConvertError::Unsupported(
                "unreduced primitive function".into(),
            ));
        }
        Err(ConvertError::Unsupported(format!(
            "agent tag {:#04x} is outside the shared fragment",
            view.tag
        )))
    }
}

/// The kernel port slot for a dnx port kind on a given agent kind.
fn kernel_slot(kind: &AgentKind, pk: PortKind) -> Option<u8> {
    match (kind, pk) {
        (_, PortKind::Principal) => Some(0),
        // dnx stores body in aux0 and var in aux1; the kernel's Abs is
        // (1=var, 2=body).
        (AgentKind::Abs, PortKind::Aux1) => Some(1),
        (AgentKind::Abs, PortKind::Aux0) => Some(2),
        // dnx stores result in aux0 and argument in aux1; the kernel's App is
        // (1=arg, 2=result).
        (AgentKind::App, PortKind::Aux1) => Some(1),
        (AgentKind::App, PortKind::Aux0) => Some(2),
        (AgentKind::Dup(_), PortKind::Aux0) => Some(1),
        (AgentKind::Dup(_), PortKind::Aux1) => Some(2),
        (AgentKind::Prim(_), PortKind::Aux0) => Some(1),
        (AgentKind::Prim(_), PortKind::Aux1) => Some(2),
        _ => None,
    }
}

fn prim_value_kind(value: &PrimValue) -> &'static str {
    match value {
        PrimValue::Int(_) | PrimValue::Float(_) | PrimValue::Bool(_) => "scalar",
        PrimValue::Str(_) => "string value",
        PrimValue::Path(_) => "path value",
        PrimValue::Null => "null",
        PrimValue::List(_) => "list",
        PrimValue::AttrSet(_) => "attribute set",
        PrimValue::Closure(_) => "native closure",
        PrimValue::Lambda => "opaque lambda",
    }
}

fn kind_name(kind: &AgentKind) -> &'static str {
    match kind {
        AgentKind::Abs => "Abs",
        AgentKind::App => "App",
        AgentKind::Dup(_) => "Dup",
        AgentKind::Era => "Era",
        AgentKind::Prim(_) => "Prim",
        AgentKind::Lit(_) => "Lit",
        AgentKind::Con(..) => "Con",
        AgentKind::Fold => "Fold",
        AgentKind::Entity(_) => "Entity",
    }
}
