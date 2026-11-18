//! A1 differential oracle (trusted.md T1 / proofs.md L1091 — φ_S-idempotency is
//! ASSERTED not proved). Generates closed pure-λ terms and checks the Δ-net
//! normalizer agrees with an INDEPENDENT, textbook normal-order β-normalizer:
//!
//!   α_eq( psi_native(normalize(elaborate(t))) , ref_nf(t) )
//!
//! The two paths share no code: `dnx_oracle::ref_nf` is a de-Bruijn
//! capture-avoiding leftmost-outermost reducer, and the dnx path is the public
//! bridge `pass1 → elaborate → normalize → psi_native`. Test-only.

use dnx_ast::{Ast, NoFun, NoVal};
use dnx_core::{normalize, DnxError, LOPath, Net, PortId, PortKind, Proper, ΔL};
use dnx_oracle::{alpha_eq, gen_term, ref_nf, LinearTerm, RefErr};
use std::collections::HashMap;
use std::sync::Arc;

type E = LinearTerm;
type Env = HashMap<Arc<str>, (PortId, u32)>;

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
// The generator (dnx-oracle) emits terms in the admissible fragment: closed,
// every binder used EXACTLY once, with a strictly-decreasing node budget. The
// reference normalizer guards the net: a term with no NF (ref Diverged) is
// discarded, so the net is only driven on guaranteed-normalizing input.

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    /// dnx-normalize ≡ ref-normalize on every generated LINEAR closed term that
    /// has a normal form. This is the A1 (φ_S-idempotency) differential oracle.
    #[test]
    fn dnx_normalize_eq_ref_normalize(term in gen_term(8)) {
        match agree(&term) {
            Ok(_) => {}                         // agreed, or ref had no NF (skipped)
            Err(msg) => prop_assert!(false, "{}", msg),
        }
    }
}
