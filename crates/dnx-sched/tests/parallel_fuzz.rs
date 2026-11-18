//! Differential fuzz for the rayon scheduler over the shared generator: every
//! generated LINEAR closed λ-term that has a normal form must reach the same
//! canonical net (by hash) under sequential and parallel reduction, and parallel
//! must never fire more β interactions than sequential.
//!
//! The generator and reference normalizer live in `dnx-oracle` so this crate and
//! `dnx-core`'s refnorm oracle fuzz exactly the same fragment.
//!
//! The defaults (300 cases, budget 6) are what CI runs. Deeper passes are opt-in
//! without editing this file:
//! `DNX_FUZZ_CASES=2000 DNX_FUZZ_BUDGET=7 cargo test -p dnx-sched --test parallel_fuzz`.

use dnx_core::{canonical_hash, LOPath, Net, PortId, PortKind, Proper, ΔL};
use dnx_oracle::{gen_term, ref_nf, LinearTerm, RefErr};
use dnx_sched::sequential::SequentialScheduler;
use dnx_sched::{normalize_par, Scheduler};
use proptest::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

type Env = HashMap<Arc<str>, (PortId, u32)>;

/// `pass1 → elaborate`, wired at the root. Same construction as the dnx path in
/// `dnx-core`'s refnorm oracle, minus the readback.
fn net_for(term: &LinearTerm) -> Result<Net<Proper, ΔL>, String> {
    let r1 = dnx_elab::pass1(term).map_err(|e| format!("pass1: {e:?}"))?;
    let mut net = Net::<Proper, ΔL>::new(256);
    let mut env = Env::new();
    let (rp, _) = dnx_elab::elaborate(
        &mut net,
        0,
        &mut env,
        LOPath::root(),
        term,
        &r1.usage_levels,
    )
    .map_err(|e| format!("elaborate: {e:?}"))?;
    let root = if rp.port_kind() == PortKind::Principal {
        rp
    } else {
        let slot = net
            .alloc_free(0)
            .map_err(|e| format!("alloc_free: {e:?}"))?;
        net.connect(rp, slot, LOPath::root())
            .map_err(|e| format!("connect: {e:?}"))?;
        slot
    };
    net.add_root(Arc::from("r"), root);
    Ok(net)
}

fn root_hash(net: &dnx_core::Net<dnx_core::Canonical, ΔL>) -> [u8; 32] {
    let root = *net.roots().get("r").expect("root r missing");
    canonical_hash(net, root).expect("canonical_hash on a pure NF")
}

/// A knob with a CI default; an unparseable value falls back rather than panicking
/// mid-fuzz.
fn tuned(key: &str, default: u32) -> u32 {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: tuned("DNX_FUZZ_CASES", 300),
        ..ProptestConfig::default()
    })]

    #[test]
    fn parallel_matches_sequential_on_generated_terms(
        term in gen_term(tuned("DNX_FUZZ_BUDGET", 6))
    ) {
        // A term with no NF would drive the net forever; the reference decides.
        if matches!(ref_nf(&term), Err(RefErr::Diverged)) {
            return Ok(());
        }
        let (seq, s_seq) = SequentialScheduler::normalize(
            net_for(&term).map_err(TestCaseError::fail)?,
        )
        .map_err(|e| TestCaseError::fail(format!("seq normalize: {e:?}")))?;
        for p in [2usize, 4] {
            let (par, s_par) = normalize_par(
                net_for(&term).map_err(TestCaseError::fail)?,
                p,
            )
            .map_err(|e| TestCaseError::fail(format!("par P={p} normalize: {e:?}")))?;
            prop_assert_eq!(
                root_hash(&seq),
                root_hash(&par),
                "term={:?} P={} hash",
                term,
                p
            );
            prop_assert!(
                s_par.r4_count <= s_seq.r4_count,
                "term={:?} P={}: par r4={} > seq r4={}",
                term,
                p,
                s_par.r4_count,
                s_seq.r4_count
            );
        }
    }
}
