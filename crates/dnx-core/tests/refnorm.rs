//! A1 differential oracle (trusted.md T1 / proofs.md L1091 — φ_S-idempotency is
//! ASSERTED not proved). Generates closed pure-λ terms and checks the Δ-net
//! normalizer agrees with an INDEPENDENT, textbook normal-order β-normalizer:
//!
//!   α_eq( psi_native(normalize(elaborate(t))) , ref_nf(t) )
//!
//! The two paths share no code: `ref_nf` is a de-Bruijn capture-avoiding
//! leftmost-outermost reducer living entirely in this file; the dnx path is the
//! public bridge `pass1 → elaborate → normalize → psi_native`. Test-only.

use dnx_ast::{Ast, NoFun, NoVal};
use dnx_core::{normalize, DnxError, LOPath, Net, PortId, PortKind, Proper, ΔL};
use std::collections::HashMap;
use std::sync::Arc;

type E = Ast<NoVal, NoFun>;
type Env = HashMap<Arc<str>, (PortId, u32)>;

// ── reference normalizer (independent oracle) ──────────────────────────────────
//
// Pure λ-calculus over de-Bruijn indices. Substitution is capture-avoiding by
// construction (shift on binder crossing); reduction is normal-order (leftmost-
// outermost) so it reaches the β-normal form whenever one exists. Fuel-bounded:
// a term with no NF (e.g. Ω) returns `RefErr::Diverged` instead of looping.

#[derive(Debug, Clone, PartialEq)]
enum Db {
    Var(u32),
    Abs(Box<Db>),
    App(Box<Db>, Box<Db>),
}

#[derive(Debug, PartialEq)]
enum RefErr {
    Diverged,
    NotClosed,
    Unsupported,
}

/// Named `Ast` → de-Bruijn. Errors on free vars (oracle is for closed terms) or
/// any non-pure-λ node (Rep/Era/Fix/Val/Fun/Perform/Handle).
fn to_db(e: &E, scope: &mut Vec<Arc<str>>) -> Result<Db, RefErr> {
    match e {
        Ast::Name(n) => scope
            .iter()
            .rev()
            .position(|b| b == n)
            .map(|i| Db::Var(i as u32))
            .ok_or(RefErr::NotClosed),
        Ast::Abs(x, body) => {
            scope.push(x.clone());
            let b = to_db(body, scope);
            scope.pop();
            Ok(Db::Abs(Box::new(b?)))
        }
        Ast::App(f, x) => Ok(Db::App(
            Box::new(to_db(f, scope)?),
            Box::new(to_db(x, scope)?),
        )),
        _ => Err(RefErr::Unsupported),
    }
}

/// Shift free indices ≥ `cutoff` by `d`.
fn shift(t: &Db, d: i64, cutoff: u32) -> Db {
    match t {
        Db::Var(i) => {
            if *i >= cutoff {
                Db::Var((*i as i64 + d) as u32)
            } else {
                Db::Var(*i)
            }
        }
        Db::Abs(b) => Db::Abs(Box::new(shift(b, d, cutoff + 1))),
        Db::App(f, x) => Db::App(Box::new(shift(f, d, cutoff)), Box::new(shift(x, d, cutoff))),
    }
}

/// `t[j := s]` — capture-avoiding (s is shifted under binders).
fn subst(t: &Db, j: u32, s: &Db) -> Db {
    match t {
        Db::Var(i) => {
            if *i == j {
                s.clone()
            } else {
                Db::Var(*i)
            }
        }
        Db::Abs(b) => Db::Abs(Box::new(subst(b, j + 1, &shift(s, 1, 0)))),
        Db::App(f, x) => Db::App(Box::new(subst(f, j, s)), Box::new(subst(x, j, s))),
    }
}

/// One leftmost-outermost β-step, if any redex exists. `None` ⇒ normal form.
fn step(t: &Db) -> Option<Db> {
    match t {
        Db::App(f, x) => {
            if let Db::Abs(body) = f.as_ref() {
                // β: (λ.body) x → body[0:=x], then renumber the freed binder.
                let sub = subst(body, 0, &shift(x, 1, 0));
                Some(shift(&sub, -1, 0))
            } else if let Some(f2) = step(f) {
                Some(Db::App(Box::new(f2), x.clone()))
            } else {
                step(x).map(|x2| Db::App(f.clone(), Box::new(x2)))
            }
        }
        Db::Abs(b) => step(b).map(|b2| Db::Abs(Box::new(b2))),
        Db::Var(_) => None,
    }
}

const FUEL: u32 = 100_000;

fn db_nf(mut t: Db) -> Result<Db, RefErr> {
    for _ in 0..FUEL {
        match step(&t) {
            Some(next) => t = next,
            None => return Ok(t),
        }
    }
    Err(RefErr::Diverged)
}

/// de-Bruijn → named `Ast`, binders named canonically `v0, v1, …` by depth.
fn from_db(t: &Db, depth: u32) -> E {
    match t {
        Db::Var(i) => Ast::Name(name(depth.saturating_sub(1).wrapping_sub(*i))),
        Db::Abs(b) => Ast::Abs(name(depth), Box::new(from_db(b, depth + 1))),
        Db::App(f, x) => Ast::App(Box::new(from_db(f, depth)), Box::new(from_db(x, depth))),
    }
}

fn name(i: u32) -> Arc<str> {
    Arc::from(format!("v{i}").as_str())
}

/// Reference β-normal form of a closed pure-λ `Ast`, as a canonical named `Ast`.
fn ref_nf(e: &E) -> Result<E, RefErr> {
    let db = to_db(e, &mut Vec::new())?;
    Ok(from_db(&db_nf(db)?, 0))
}

// ── dnx net path (public bridge) ───────────────────────────────────────────────

/// `pass1 → elaborate → normalize → psi_native`. Errors propagate (no unwrap).
fn dnx_nf(expr: &E) -> Result<E, DnxError> {
    dnx_nf_stats(expr).map(|(ast, _)| ast)
}

/// As `dnx_nf`, also returning the reducer's stats.
fn dnx_nf_stats(expr: &E) -> Result<(E, dnx_core::ReduceStats), DnxError> {
    let r1 = dnx_elab::pass1(expr)?;
    let mut net = Net::<Proper, ΔL>::new(256);
    let mut env = Env::new();
    let (rp, _) = dnx_elab::elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        expr,
        &r1.usage_levels,
    )?;
    let root = if rp.port_kind() == PortKind::Principal {
        rp
    } else {
        let slot = net.alloc_free(0)?;
        net.connect(rp, slot, LOPath::root())?;
        slot
    };
    net.add_root("r".into(), root);
    let (canonical, stats) = normalize(net)?;
    match dnx_read::psi_native::<ΔL, NoVal, NoFun>(&canonical) {
        dnx_read::ReadbackResult::Lambda(ast) => Ok((ast, stats)),
        dnx_read::ReadbackResult::Partial(_) => Err(DnxError::ReadbackIncomplete),
    }
}

// ── α-equivalence on readback ASTs ─────────────────────────────────────────────

fn alpha_eq(a: &E, b: &E) -> bool {
    alpha(a, b, &mut Vec::new(), &mut Vec::new())
}

fn alpha(a: &E, b: &E, sa: &mut Vec<Arc<str>>, sb: &mut Vec<Arc<str>>) -> bool {
    match (a, b) {
        (Ast::Name(x), Ast::Name(y)) => {
            match (
                sa.iter().rposition(|n| n == x),
                sb.iter().rposition(|n| n == y),
            ) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false,
            }
        }
        (Ast::Abs(x, bx), Ast::Abs(y, by)) => {
            sa.push(x.clone());
            sb.push(y.clone());
            let r = alpha(bx, by, sa, sb);
            sa.pop();
            sb.pop();
            r
        }
        (Ast::App(f1, x1), Ast::App(f2, x2)) => alpha(f1, f2, sa, sb) && alpha(x1, x2, sa, sb),
        // psi_native wraps unused binders in `Era(Name, body)`; the reference NF
        // has no such marker, so compare the Era body against the other side.
        (Ast::Era(_, body), other) | (other, Ast::Era(_, body)) => alpha(body, other, sa, sb),
        _ => false,
    }
}

// ── smoke: bridge + ref agree on hand-written closed terms ─────────────────────

fn nm(s: &str) -> E {
    Ast::Name(Arc::from(s))
}
fn ab(x: &str, b: E) -> E {
    Ast::Abs(Arc::from(x), Box::new(b))
}
fn ap(f: E, x: E) -> E {
    Ast::App(Box::new(f), Box::new(x))
}

/// Compare the two normalizers on one closed term. Returns Ok(true) when both
/// agree, Ok(false) when the reference has no NF (skip — nothing to compare),
/// Err on a genuine disagreement or a net failure where the reference succeeded.
fn agree(term: &E) -> Result<bool, String> {
    let reference = match ref_nf(term) {
        Ok(nf) => nf,
        Err(RefErr::Diverged) => return Ok(false),
        Err(e) => return Err(format!("ref rejected closed term: {e:?}")),
    };
    let dnx =
        dnx_nf(term).map_err(|e| format!("dnx failed but ref has NF {reference:?}: {e:?}"))?;
    if alpha_eq(&dnx, &reference) {
        Ok(true)
    } else {
        Err(format!(
            "DISAGREE term={term:?} dnx={dnx:?} ref={reference:?}"
        ))
    }
}

// ── corpus: hand-written LINEAR closed terms ───────────────────────────────────
//
// The dnx surface λ is LINEAR (pass1.rs:78-83): every ordinary binder is used
// EXACTLY once; duplication needs an explicit `Rep`, deletion an explicit `Era`.
// So K (`λx.λy.x`) and S (which duplicate/discard) are NOT admissible without
// fan nodes — the corpus stays inside the pure-linear fragment the oracle covers.

fn corpus() -> Vec<E> {
    let id = || ab("x", nm("x"));
    // B = λf.λg.λx. f (g x) — each of f,g,x used once (linear).
    let b = || ab("f", ab("g", ab("x", ap(nm("f"), ap(nm("g"), nm("x"))))));
    vec![
        // Linear normal forms (their own NF).
        id(),
        b(),
        ab("f", ab("x", ap(nm("f"), nm("x")))), // λf.λx. f x
        // β-redexes that collapse, all linear.
        ap(id(), id()),                                   // I I → I
        ap(ab("f", ab("x", ap(nm("f"), nm("x")))), id()), // (λf.λx.f x) I → λx. I x → λx.x
        ap(ap(ap(b(), id()), id()), ab("w", nm("w"))),    // B I I w → w
        // nested redex under a binder.
        ab("q", ap(id(), nm("q"))), // λq. I q → λq.q
        // deeper linear chain.
        ap(ap(b(), id()), id()), // B I I → λx. I (I x)
    ]
}

#[test]
fn diag_partial_app() -> Result<(), DnxError> {
    let s = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let term = ap(s, ab("y", nm("y"))); // (λf.λx.f x) I
    let r1 = dnx_elab::pass1(&term)?;
    println!("DIAG pass1 ok era={} rep={}", r1.era_used, r1.rep_used);
    let mut net = Net::<Proper, ΔL>::new(256);
    let mut env = Env::new();
    let elab = dnx_elab::elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        &term,
        &r1.usage_levels,
    );
    println!(
        "DIAG elaborate = {:?}",
        elab.as_ref().map(|(p, l)| (p.port_kind(), *l))
    );
    let (rp, _) = elab?;
    let root = if rp.port_kind() == PortKind::Principal {
        rp
    } else {
        let slot = net.alloc_free(0)?;
        net.connect(rp, slot, LOPath::root())?;
        slot
    };
    net.add_root("r".into(), root);
    let (canonical, stats) = normalize(net)?;
    let rb = match dnx_read::psi_native::<ΔL, NoVal, NoFun>(&canonical) {
        dnx_read::ReadbackResult::Lambda(a) => format!("Lambda({a:?})"),
        dnx_read::ReadbackResult::Partial(n) => format!("Partial({n})"),
    };
    println!(
        "DIAG r4={} interactions={} rb={rb}",
        stats.r4_count, stats.interactions
    );
    Ok(())
}

/// Regression: R4 (β) cross-wires a body's principal straight to the open root
/// free slot. The resulting principal⊗free-slot pair is a wire endpoint, not a
/// redex, so no rule applies — it must be skipped quietly (complete readback)
/// instead of reaching `dispatch_phase1`'s catch-all as `ReadbackIncomplete`,
/// and it must not be counted as an interaction.
#[test]
fn beta_body_wired_to_root_free_slot_normalizes() -> Result<(), String> {
    // (λf.λx.f x) I  →β  λx. I x  →β  λx.x ; the inner β wires I's body directly
    // to the root free slot.
    let s = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let term = ap(s, ab("y", nm("y")));
    let reference = ref_nf(&term).map_err(|e| format!("ref rejected closed term: {e:?}"))?;
    let (dnx, stats) = dnx_nf_stats(&term).map_err(|e| format!("dnx failed: {e:?}"))?;
    assert!(alpha_eq(&dnx, &reference), "dnx={dnx:?} ref={reference:?}");
    // Two β-steps and nothing else: the free-slot wire pair contributes no
    // interaction (with the bug it was counted, making three).
    assert_eq!(stats.interactions, 2, "stats={stats:?}");
    assert_eq!(stats.r4_count, 2, "stats={stats:?}");
    Ok(())
}

#[test]
fn smoke_bridge_matches_ref() -> Result<(), String> {
    // (λf.λx. f x)(λy.y)(λz.z)  →β  λz.z
    let s = ab("f", ab("x", ap(nm("f"), nm("x"))));
    let term = ap(ap(s, ab("y", nm("y"))), ab("z", nm("z")));
    assert!(agree(&term)?, "term has a NF, must compare");
    Ok(())
}

#[test]
fn corpus_bridge_matches_ref() -> Result<(), String> {
    for (i, term) in corpus().into_iter().enumerate() {
        agree(&term).map_err(|e| format!("corpus[{i}] {term:?}: {e}"))?;
    }
    Ok(())
}

// ── D2 differential fuzz: generated LINEAR closed λ-terms ──────────────────────
//
// The generator emits terms in the admissible fragment (pass1.rs:78-83): closed,
// every binder used EXACTLY once. `build` produces a term whose free variables
// are precisely `vars`, each occurring once:
//   • |vars|==1  → that variable (leaf, consumes it);
//   • Abs        → bind a fresh name, body must use `vars ∪ {fresh}`;
//   • App(f,x)   → DISJOINT split `vars = Sf ⊎ Sx` (linearity: no overlap).
// The whole term starts with `vars = ∅` ⇒ closed. `budget` is the number of
// structural nodes the term may add; it strictly decreases on every recursive
// step (an App at zero budget bisects the variables instead and needs no budget,
// so leaves are always reachable). The term is built from a fixed bit tape rather
// than a recursive strategy, so construction cannot recurse before sampling and
// the size budget is respected. The reference normalizer guards the net: a term
// with no NF (ref Diverged) is discarded, so the net is only driven on
// guaranteed-normalizing input and cannot hang.

use proptest::prelude::*;

fn next_bit(tape: &mut impl Iterator<Item = bool>) -> bool {
    tape.next().unwrap_or(false)
}

fn take_bits(tape: &mut impl Iterator<Item = bool>, n: u32) -> u32 {
    (0..n).fold(0, |acc, _| (acc << 1) | u32::from(next_bit(tape)))
}

fn fresh_name(fresh: &mut u32) -> Arc<str> {
    let name: Arc<str> = Arc::from(format!("g{fresh}").as_str());
    *fresh += 1;
    name
}

/// Disjoint partition of `vars`: with `proper`, both sides are non-empty (an App
/// at zero budget relies on this, since it cannot spend budget to split again).
fn partition(
    vars: &mut Vec<Arc<str>>,
    tape: &mut impl Iterator<Item = bool>,
    proper: bool,
) -> (Vec<Arc<str>>, Vec<Arc<str>>) {
    let n = vars.len();
    let k = if proper {
        1 + (take_bits(tape, 8) as usize) % (n - 1)
    } else {
        (take_bits(tape, 8) as usize) % (n + 1)
    };
    let right = vars.split_off(k);
    (std::mem::take(vars), right)
}

fn build(
    vars: &mut Vec<Arc<str>>,
    fresh: &mut u32,
    budget: u32,
    tape: &mut impl Iterator<Item = bool>,
) -> E {
    match vars.len() {
        // Nothing to consume: only an Abs (which binds and uses its variable)
        // keeps the term linear and closed. This adds no free variables.
        0 => {
            let f = fresh_name(fresh);
            Ast::Abs(f.clone(), Box::new(Ast::Name(f)))
        }
        // One variable left and no budget: it must be consumed as a leaf.
        1 if budget == 0 => Ast::Name(vars.pop().expect("one variable")),
        // One variable left with budget: leaf, bind one more under it, or apply.
        1 => match take_bits(tape, 2) {
            0 => Ast::Name(vars.pop().expect("one variable")),
            1 => {
                let f = fresh_name(fresh);
                vars.push(f.clone());
                let body = build(vars, fresh, budget - 1, tape);
                Ast::Abs(f, Box::new(body))
            }
            _ => {
                let (mut l, mut r) = partition(vars, tape, false);
                let half = budget.saturating_sub(1) / 2;
                let f = build(&mut l, fresh, half, tape);
                let x = build(&mut r, fresh, half, tape);
                Ast::App(Box::new(f), Box::new(x))
            }
        },
        // Several variables: they have to be distributed by an App; with budget
        // left one of them may be bound under an Abs instead.
        _ => {
            let bind = budget > 0 && take_bits(tape, 2) == 0;
            if bind {
                let f = fresh_name(fresh);
                vars.push(f.clone());
                let body = build(vars, fresh, budget - 1, tape);
                Ast::Abs(f, Box::new(body))
            } else {
                let (mut l, mut r) = partition(vars, tape, budget == 0);
                let half = budget.saturating_sub(1) / 2;
                let f = build(&mut l, fresh, half, tape);
                let x = build(&mut r, fresh, half, tape);
                Ast::App(Box::new(f), Box::new(x))
            }
        }
    }
}

/// Strategy: a random bit tape, decoded into a linear closed term.
fn gen_term(budget: u32) -> impl Strategy<Value = E> {
    proptest::collection::vec(any::<bool>(), 512).prop_map(move |bits| {
        let mut tape = bits.into_iter();
        let mut fresh = 0;
        build(&mut Vec::new(), &mut fresh, budget, &mut tape)
    })
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    /// dnx-normalize ≡ ref-normalize on every generated LINEAR closed term that
    /// has a normal form. This is the A1 (φ_S-idempotency) differential oracle.
    #[test]
    fn dnx_normalize_eq_ref_normalize(term in gen_term(6)) {
        match agree(&term) {
            Ok(_) => {}                         // agreed, or ref had no NF (skipped)
            Err(msg) => prop_assert!(false, "{}", msg),
        }
    }
}
