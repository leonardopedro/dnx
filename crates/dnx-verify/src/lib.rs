//! Verify a Nix → AustralVM translation by comparing the two DeltaNets.
//!
//! Both sides are reduced to a unique normal form and hashed by the *same*
//! canonical serializer — the one in the AustralVM kernel's DeltaNet
//! implementation (`unfer/logos/src/deltanet/unf.rs`). Equality of that digest
//! is equality of the canonical net serialization, and the kernel's
//! isomorphism witness is then produced to certify the node permutation.
//!
//! This is not a value comparison: two nets that compute the same number but
//! have different normal forms (for example `x + x` and `2 * x`) hash
//! differently, exactly as the kernel's `austral_defeq` reports them.
//!
//! # Supported fragment
//!
//! The Nix side is exported into the kernel's `Net`, so only constructs with a
//! faithful kernel encoding can be compared: closed terms whose normal form is
//! built from abstractions, applications, duplicators, erasers and
//! `Int64`/`F64`/`Bool` literals. Open terms, strings and other primitive
//! values, and unresolvable primitive functions are reported as
//! [`VerifyError::Unsupported`] rather than approximated.
//!
//! # Nets with entities
//!
//! An Austral module whose `main` uses a constructor or an unresolved name
//! reduces to a net with `Entity` agents, which no Nix expression can produce.
//! [`austral_check`] compares two Austral nets structurally for that case — a
//! translated module against a reference module — and [`Side::entities`] lists
//! the opaque names each side carries. Entity names are part of the canonical
//! serialization, so `ExitSuccess` and `ExitFailure` are different terms, while
//! the same name at different positions is still matched by the isomorphism
//! witness.

pub mod convert;

use convert::ConvertError;
use dnx_core::prim::{PrimState, PrimValue};
use dnx_core::{Canonical, Net, PortId, ΔK};
use dnx_lang::runtime::NixRuntime;
use logos::deltanet::{unf_hash_string, Net as KernelNet};

#[derive(Debug)]
pub enum VerifyError {
    /// The Nix expression failed to parse, elaborate or normalize.
    Nix(String),
    /// The Austral source failed to translate to a DeltaNet.
    Austral(String),
    /// The Nix net uses a construct the kernel net cannot encode.
    Unsupported(String),
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerifyError::Nix(m) => write!(f, "nix: {m}"),
            VerifyError::Austral(m) => write!(f, "austral: {m}"),
            VerifyError::Unsupported(m) => write!(f, "unsupported: {m}"),
        }
    }
}

impl std::error::Error for VerifyError {}

impl From<ConvertError> for VerifyError {
    fn from(e: ConvertError) -> Self {
        match e {
            ConvertError::Unsupported(m) => VerifyError::Unsupported(m),
            ConvertError::Malformed(m) => VerifyError::Nix(m),
        }
    }
}

/// One side of the comparison, in the kernel's net representation.
#[derive(Debug)]
pub struct Side {
    pub net: KernelNet,
    pub hash: String,
    /// Reachable live agents in the net.
    pub agents: usize,
    /// The closed scalar the side reduced to, when it has one.
    pub value: Option<String>,
    /// Reachable `Entity` names, sorted and deduplicated. These are the opaque
    /// names (constructors and unresolved functions) the side still mentions.
    pub entities: Vec<String>,
}

impl Side {
    fn new(net: KernelNet, value: Option<String>) -> Result<Self, VerifyError> {
        let hash = unf_hash_string(&net).map_err(VerifyError::Unsupported)?;
        let agents = reachable_nodes(&net);
        let entities = reachable_entities(&net);
        Ok(Side {
            net,
            hash,
            agents,
            value,
            entities,
        })
    }
}

/// Live nodes reachable from `net.root` — the part the canonical hash covers.
///
/// Reduction leaves unreachable nodes behind (e.g. the literals a primitive
/// consumed); counting every live node would overstate the net the digest
/// actually identifies.
fn reachable_nodes(net: &KernelNet) -> usize {
    use std::collections::{HashSet, VecDeque};
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([net.root.clone()]);
    while let Some(port) = queue.pop_front() {
        let resolved = net.resolve_port(&port);
        let Some(Some(node)) = net.nodes.get(resolved.node as usize) else {
            continue;
        };
        if node.freed || !seen.insert(resolved.node) {
            continue;
        }
        for child in node.ports.iter().flatten() {
            queue.push_back(child.clone());
        }
    }
    seen.len()
}

/// Reachable `Entity` names in canonical (depth-first) order, deduplicated.
fn reachable_entities(net: &KernelNet) -> Vec<String> {
    use logos::deltanet::AgentKind;
    use std::collections::HashSet;

    let mut seen_nodes = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut names = Vec::new();
    let mut stack = vec![net.root.clone()];
    while let Some(port) = stack.pop() {
        let resolved = net.resolve_port(&port);
        let Some(Some(node)) = net.nodes.get(resolved.node as usize) else {
            continue;
        };
        if node.freed || !seen_nodes.insert(resolved.node) {
            continue;
        }
        if let AgentKind::Entity(name) = &node.kind {
            if seen_names.insert(name.clone()) {
                names.push(name.clone());
            }
        }
        for child in node.ports.iter().flatten() {
            stack.push(child.clone());
        }
    }
    names.sort();
    names
}

/// A completed comparison.
#[derive(Debug)]
pub enum Verdict {
    Equivalent {
        left: Side,
        right: Side,
        /// Size of the isomorphism witness (canonical positions covered).
        witness_pairs: usize,
    },
    Different {
        left: Side,
        right: Side,
    },
}

/// Compile a Nix expression to its canonical DeltaNet and hash it.
pub fn nix_side(expr: &str) -> Result<Side, VerifyError> {
    let (net, prim, root) = NixRuntime::pure()
        .eval_net(expr)
        .map_err(|e| VerifyError::Nix(e.to_string()))?;
    let value = root_value(&net, &prim, root);
    let net = convert::to_kernel_net(&net, &prim, root)?;
    Side::new(net, value)
}

/// Compile an AustralVM source fragment to its canonical DeltaNet and hash it.
pub fn austral_side(source: &str) -> Result<Side, VerifyError> {
    let translation =
        logos::translate::translate_austral_any(source).map_err(VerifyError::Austral)?;
    let value = translation.value.as_ref().map(|v| v.to_string());
    Side::new(translation.net, value)
}

/// Reduce both sides and compare their canonical DeltaNet identities.
pub fn check(nix_expr: &str, austral_source: &str) -> Result<Verdict, VerifyError> {
    let nix = nix_side(nix_expr)?;
    let austral = austral_side(austral_source)?;
    compare(nix, austral)
}

/// Compare two AustralVM sources structurally, including nets that still
/// contain `Entity` agents.
///
/// This is the check for modules whose `main` reduces to a constructor call or
/// an unresolved function: the reference is the known-good module and the
/// translation is the one under test. Both sides must mention the same entity
/// names; the names are part of the canonical identity, so a renamed
/// constructor is a mismatch rather than an isomorphism.
pub fn austral_check(reference: &str, translated: &str) -> Result<Verdict, VerifyError> {
    let reference = austral_side(reference)?;
    let translated = austral_side(translated)?;
    compare(reference, translated)
}

fn compare(left: Side, right: Side) -> Result<Verdict, VerifyError> {
    if left.hash != right.hash {
        return Ok(Verdict::Different { left, right });
    }
    let witness = logos::deltanet::isomorphism_witness(&left.net, &right.net)
        .map_err(VerifyError::Unsupported)?;
    let witness_pairs = witness.as_ref().map(|w| w.len()).unwrap_or(0);
    Ok(Verdict::Equivalent {
        left,
        right,
        witness_pairs,
    })
}

/// Human-readable detail for a primitive value, used by the CLI.
pub(crate) fn describe_prim(v: &PrimValue) -> String {
    match v {
        PrimValue::Int(n) => n.to_string(),
        PrimValue::Float(x) => x.to_string(),
        PrimValue::Bool(b) => b.to_string(),
        PrimValue::Str(s) => format!("{s:?}"),
        other => format!("{other:?}"),
    }
}

/// One translation pair in a batch manifest.
///
/// Manifest format (JSON; a bare array or `{"pairs": [...]}`):
///
/// ```json
/// {"pairs": [
///   {"name": "arith", "nix": "arith.nix", "austral": "Arith.aum"},
///   {"nix": "bool.nix", "austral": "bool.aum"}
/// ]}
/// ```
///
/// Paths are resolved relative to the manifest's directory. `name` is
/// optional and defaults to the Nix file's stem. `expect` is optional and
/// records the verdict the pair is *required* to have — `"equivalent"` or
/// `"different"` — so a known-bad translation can stay in a manifest without
/// making the batch fail.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct PairSpec {
    #[serde(default)]
    pub name: Option<String>,
    pub nix: String,
    pub austral: String,
    /// Validated by [`load_manifest`] into an [`Expected`].
    #[serde(default)]
    pub expect: Option<String>,
}

/// A verdict a manifest can require for a pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expected {
    Equivalent,
    Different,
}

impl Expected {
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "equivalent" => Some(Self::Equivalent),
            "different" => Some(Self::Different),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Equivalent => "equivalent",
            Self::Different => "different",
        }
    }
}

#[derive(Debug, serde::Deserialize)]
#[serde(untagged)]
enum ManifestFile {
    List(Vec<PairSpec>),
    Wrapped { pairs: Vec<PairSpec> },
}

/// Read and parse a batch manifest. Errors are manifest-level (unreadable or
/// malformed), never a verdict about a pair.
pub fn load_manifest(path: &std::path::Path) -> Result<Vec<PairSpec>, String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("manifest {}: {e}", path.display()))?;
    let manifest: ManifestFile =
        serde_json::from_str(&text).map_err(|e| format!("manifest {}: {e}", path.display()))?;
    let pairs = match manifest {
        ManifestFile::List(pairs) => pairs,
        ManifestFile::Wrapped { pairs } => pairs,
    };
    if pairs.is_empty() {
        return Err(format!("manifest {}: no pairs", path.display()));
    }
    for (i, pair) in pairs.iter().enumerate() {
        if pair.nix.trim().is_empty() || pair.austral.trim().is_empty() {
            return Err(format!(
                "manifest {}: pair {} has an empty source path",
                path.display(),
                i + 1
            ));
        }
        if let Some(raw) = pair
            .expect
            .as_deref()
            .filter(|raw| Expected::parse(raw).is_none())
        {
            return Err(format!(
                "manifest {}: pair {} has unknown `expect` `{raw}` (use `equivalent` or `different`)",
                path.display(),
                i + 1
            ));
        }
    }
    Ok(pairs)
}

/// One Nix/AustralVM pair found by [`scan_dir`].
#[derive(Debug, Clone)]
pub struct ScannedPair {
    /// Path stem relative to the scanned directory, e.g. `sub/arith`.
    pub name: String,
    pub nix: std::path::PathBuf,
    pub austral: std::path::PathBuf,
}

/// The result of scanning a translation-output directory.
#[derive(Debug)]
pub struct ScanReport {
    pub pairs: Vec<ScannedPair>,
    /// Files with no counterpart at the same stem (reported, not fatal).
    pub unpaired: Vec<std::path::PathBuf>,
}

/// Pair `*.nix` with `*.aum` files by their path stem under `dir`.
///
/// `foo.nix` pairs with `foo.aum` in the same directory; the walk is recursive,
/// skips hidden directories and `target`, and sorts everything so the generated
/// manifest is stable. Files are matched by stem only, so a folder with two
/// Nix entry points for one module (`default.nix`, `package.nix`) leaves both
/// unpaired rather than guessing which is the translation subject.
pub fn scan_dir(dir: &std::path::Path) -> Result<ScanReport, String> {
    use std::collections::BTreeMap;

    let mut files = Vec::new();
    collect_sources(dir, &mut files)?;

    let mut nix: BTreeMap<std::path::PathBuf, std::path::PathBuf> = BTreeMap::new();
    let mut austral: BTreeMap<std::path::PathBuf, std::path::PathBuf> = BTreeMap::new();
    for path in files {
        let stem = path
            .strip_prefix(dir)
            .map_err(|_| format!("{}: not under {}", path.display(), dir.display()))?
            .with_extension("");
        let is_nix = path.extension().and_then(|e| e.to_str()) == Some("nix");
        if is_nix {
            nix.insert(stem, path);
        } else {
            austral.insert(stem, path);
        }
    }

    let mut pairs = Vec::new();
    let mut unpaired = Vec::new();
    let stems: std::collections::BTreeSet<_> = nix.keys().chain(austral.keys()).cloned().collect();
    for stem in stems {
        match (nix.remove(&stem), austral.remove(&stem)) {
            (Some(nix), Some(austral)) => pairs.push(ScannedPair {
                name: stem.to_string_lossy().replace('\\', "/"),
                nix,
                austral,
            }),
            (Some(nix), None) => unpaired.push(nix),
            (None, Some(austral)) => unpaired.push(austral),
            (None, None) => {}
        }
    }
    unpaired.sort();
    Ok(ScanReport { pairs, unpaired })
}

fn collect_sources(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) -> Result<(), String> {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .map_err(|e| format!("scan {}: {e}", dir.display()))?
        .collect::<Result<_, _>>()
        .map_err(|e| format!("scan {}: {e}", dir.display()))?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let name = entry.file_name();
        if path.is_dir() {
            let name = name.to_string_lossy();
            if name.starts_with('.') || name == "target" {
                continue;
            }
            collect_sources(&path, out)?;
        } else if entry.file_type().map(|t| t.is_file()).unwrap_or(false)
            && matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("nix" | "aum")
            )
        {
            out.push(path);
        }
    }
    Ok(())
}

/// Render a starter manifest for `pairs`, with paths relative to `base` (the
/// directory the manifest will live in).
pub fn manifest_json(pairs: &[ScannedPair], base: &std::path::Path) -> String {
    manifest_json_with_expectations(pairs, base, &std::collections::BTreeMap::new())
}

/// Like [`manifest_json`], but carries over the `expect` declarations of an
/// existing manifest at `previous` for pairs that keep their name.
///
/// Regenerating a folder's manifest must not silently turn a recorded
/// known-bad translation back into an expected pass; a name that is gone from
/// the folder simply drops its declaration, and an unreadable `previous`
/// contributes nothing.
pub fn manifest_json_preserving(
    pairs: &[ScannedPair],
    base: &std::path::Path,
    previous: &std::path::Path,
) -> String {
    let mut expectations = std::collections::BTreeMap::new();
    if let Ok(previous_pairs) = load_manifest(previous) {
        for (index, spec) in previous_pairs.iter().enumerate() {
            if let Some(expected) = spec.expect.as_deref().and_then(Expected::parse) {
                expectations.insert(spec_name(spec, index), expected);
            }
        }
    }
    manifest_json_with_expectations(pairs, base, &expectations)
}

fn manifest_json_with_expectations(
    pairs: &[ScannedPair],
    base: &std::path::Path,
    expectations: &std::collections::BTreeMap<String, Expected>,
) -> String {
    let entries: Vec<serde_json::Value> = pairs
        .iter()
        .map(|pair| {
            let mut entry = serde_json::json!({
                "name": pair.name,
                "nix": relative_path(base, &pair.nix),
                "austral": relative_path(base, &pair.austral),
            });
            if let Some(expected) = expectations.get(&pair.name) {
                entry["expect"] = serde_json::json!(expected.as_str());
            }
            entry
        })
        .collect();
    serde_json::to_string_pretty(&serde_json::json!({ "pairs": entries }))
        .expect("a manifest of strings always serializes")
}

/// A path for `target` relative to `base`, or `target` itself when the two have
/// no common root (which only happens across Windows drives).
fn relative_path(base: &std::path::Path, target: &std::path::Path) -> String {
    let canonical = |p: &std::path::Path| std::fs::canonicalize(p).unwrap_or_else(|_| p.into());
    let base = canonical(base);
    let target = canonical(target);
    let b: Vec<_> = base.components().collect();
    let t: Vec<_> = target.components().collect();
    if b.first() != t.first() {
        return target.to_string_lossy().into_owned();
    }
    let common = b.iter().zip(&t).take_while(|(a, b)| a == b).count();
    let mut out = std::path::PathBuf::new();
    for _ in common..b.len() {
        out.push("..");
    }
    for component in &t[common..] {
        out.push(component.as_os_str());
    }
    if out.as_os_str().is_empty() {
        out.push(".");
    }
    out.to_string_lossy().replace('\\', "/")
}

/// The outcome for one manifest entry.
pub struct PairReport {
    pub name: String,
    /// The verdict the manifest required, when it declared one.
    pub expected: Option<Expected>,
    pub verdict: Result<Verdict, VerifyError>,
}

impl PairReport {
    /// Whether the observed verdict is the one the manifest asked for: an
    /// equivalent verdict when no expectation is declared, otherwise exactly
    /// the declared one. Errors never pass.
    pub fn passed(&self) -> bool {
        match (&self.expected, &self.verdict) {
            (_, Err(_)) => false,
            (None, Ok(Verdict::Equivalent { .. })) => true,
            (Some(Expected::Equivalent), Ok(Verdict::Equivalent { .. })) => true,
            (Some(Expected::Different), Ok(Verdict::Different { .. })) => true,
            _ => false,
        }
    }

    /// Whether a declared expectation was contradicted by a comparable
    /// verdict. Errors are reported as errors, not as unmet expectations.
    pub fn is_unexpected(&self) -> bool {
        self.expected.is_some() && self.verdict.is_ok() && !self.passed()
    }
}

fn spec_name(pair: &PairSpec, index: usize) -> String {
    pair.name
        .clone()
        .or_else(|| {
            std::path::Path::new(&pair.nix)
                .file_stem()
                .map(|s| s.to_string_lossy().into_owned())
        })
        .unwrap_or_else(|| format!("pair {}", index + 1))
}

/// Check every pair in a manifest, resolving paths against `base`.
///
/// One failing pair does not stop the batch: `read` and comparison errors are
/// reported in its own [`PairReport`].
pub fn check_pairs(pairs: &[PairSpec], base: &std::path::Path) -> Vec<PairReport> {
    pairs
        .iter()
        .enumerate()
        .map(|(index, pair)| {
            let name = spec_name(pair, index);
            let nix_path = resolve_path(base, &pair.nix);
            let austral_path = resolve_path(base, &pair.austral);
            let verdict = (|| {
                let nix = std::fs::read_to_string(&nix_path)
                    .map_err(|e| VerifyError::Nix(format!("read {}: {e}", nix_path.display())))?;
                let austral = std::fs::read_to_string(&austral_path).map_err(|e| {
                    VerifyError::Austral(format!("read {}: {e}", austral_path.display()))
                })?;
                check(&nix, &austral)
            })();
            PairReport {
                name,
                expected: pair.expect.as_deref().and_then(Expected::parse),
                verdict,
            }
        })
        .collect()
}

fn resolve_path(base: &std::path::Path, path: &str) -> std::path::PathBuf {
    let path = std::path::Path::new(path);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    }
}

/// Render the scalar at the Nix root, when it is a primitive value.
///
/// Informational output only: the verdict compares the nets, never this string.
pub(crate) fn root_value(
    net: &Net<Canonical, ΔK>,
    prim: &PrimState,
    root: PortId,
) -> Option<String> {
    let mut p = root;
    for _ in 0..8 {
        if p.is_null() || p.is_eraser() {
            return None;
        }
        let view = net.slot_view_at(p.slot_idx())?;
        if view.is_free() {
            p = PortId::from_raw(view.principal);
            continue;
        }
        if view.is_prim_val() {
            return prim.vals.get(view.data as usize).map(describe_prim);
        }
        return None;
    }
    None
}
