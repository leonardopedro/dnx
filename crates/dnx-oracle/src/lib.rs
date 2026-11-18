//! Shared differential-test oracle: a generator of LINEAR closed pure-λ terms
//! and an INDEPENDENT, textbook normal-order β-normalizer to compare against.
//!
//! The dnx surface λ is linear (`pass1.rs:78-83`: every ordinary binder is used
//! EXACTLY once; duplication needs an explicit `Rep`, deletion an explicit
//! `Era`), so the generator stays inside that fragment. It exists so more than
//! one crate can fuzz its own reducer path against the same terms: `dnx-core`'s
//! sequential oracle, `dnx-sched`'s parallel-vs-sequential gate, etc.
//!
//! The reference normalizer shares no code with dnx: de-Bruijn, capture-avoiding
//! substitution, leftmost-outermost reduction, fuel-bounded (`RefErr::Diverged`
//! instead of looping, so a caller can skip a term with no normal form).

use dnx_ast::{Ast, NoFun, NoVal};

/// The term type the generator produces (and the reference normalizer consumes).
pub type LinearTerm = Ast<NoVal, NoFun>;

type E = LinearTerm;

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

/// Why the reference normalizer could not produce a normal form.
#[derive(Debug, PartialEq)]
pub enum RefErr {
    Diverged,
    NotClosed,
    Unsupported,
}

/// Named `Ast` → de-Bruijn. Errors on free vars (oracle is for closed terms) or
/// any non-pure-λ node (Rep/Era/Fix/Val/Fun/Perform/Handle).
fn to_db(e: &E, scope: &mut Vec<std::sync::Arc<str>>) -> Result<Db, RefErr> {
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

fn name(i: u32) -> std::sync::Arc<str> {
    std::sync::Arc::from(format!("v{i}").as_str())
}

/// Reference β-normal form of a closed pure-λ `Ast`, as a canonical named `Ast`.
pub fn ref_nf(e: &E) -> Result<E, RefErr> {
    let db = to_db(e, &mut Vec::new())?;
    Ok(from_db(&db_nf(db)?, 0))
}

// ── α-equivalence on readback ASTs ─────────────────────────────────────────────

/// α-equivalence of two readback ASTs. Unused binders may be wrapped in
/// `Era(Name, body)` by dnx's readback; the reference NF has no such marker, so
/// an `Era` is compared through its body.
pub fn alpha_eq(a: &E, b: &E) -> bool {
    alpha(a, b, &mut Vec::new(), &mut Vec::new())
}

fn alpha(
    a: &E,
    b: &E,
    sa: &mut Vec<std::sync::Arc<str>>,
    sb: &mut Vec<std::sync::Arc<str>>,
) -> bool {
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
        (Ast::Era(_, body), other) | (other, Ast::Era(_, body)) => alpha(body, other, sa, sb),
        _ => false,
    }
}

// ── generator: LINEAR closed pure-λ terms ─────────────────────────────────────
//
// `build` produces a term whose free variables are precisely `vars`, each
// occurring once:
//   • |vars|==0  → closed: an Abs binding a fresh variable (recursing into the
//                  budget) or, at zero budget, the linear identity;
//   • |vars|==1  → that variable (leaf, consumes it), bind one more under it,
//                  or apply (a disjoint split can leave one side empty);
//   • Abs        → bind a fresh name, body must use `vars ∪ {fresh}`;
//   • App(f,x)   → DISJOINT split `vars = Sf ⊎ Sx` (linearity: no overlap).
// `budget` is the number of structural nodes the term may add; it strictly
// decreases on every recursive step (an App at zero budget bisects the variables
// instead and needs no budget, so leaves are always reachable). The term is built
// from a fixed bit tape rather than a recursive strategy, so construction cannot
// recurse before sampling and the size budget is respected.

use proptest::prelude::*;
use std::sync::Arc;

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

/// Decode a bit tape into one linear closed term with at most `budget` extra
/// structural nodes.
pub fn build(
    vars: &mut Vec<Arc<str>>,
    fresh: &mut u32,
    budget: u32,
    tape: &mut impl Iterator<Item = bool>,
) -> E {
    match vars.len() {
        // Nothing to consume: the subterm must be closed, so the only admissible
        // shape is an Abs that binds a fresh variable and uses it in its body.
        // With budget left the body is built with that variable pending (so real
        // structure appears); at zero budget it is the linear identity.
        0 if budget == 0 => {
            let f = fresh_name(fresh);
            Ast::Abs(f.clone(), Box::new(Ast::Name(f)))
        }
        0 => {
            let f = fresh_name(fresh);
            let body = build(&mut vec![f.clone()], fresh, budget - 1, tape);
            Ast::Abs(f, Box::new(body))
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

/// Strategy: a random bit tape, decoded into a linear closed term with at most
/// `budget` extra structural nodes. Every generated term is closed and uses each
/// binder exactly once, i.e. it lies in the fragment `pass1` admits.
pub fn gen_term(budget: u32) -> impl Strategy<Value = LinearTerm> {
    proptest::collection::vec(any::<bool>(), 512).prop_map(move |bits| {
        let mut tape = bits.into_iter();
        let mut fresh = 0;
        build(&mut Vec::new(), &mut fresh, budget, &mut tape)
    })
}
