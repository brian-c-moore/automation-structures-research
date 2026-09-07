//! Reference validation for **Buchberger's algorithm**.
//!
//! Same two kinds of check as Knuth-Bendix completion:
//!
//! * **Literature anchor.** Two standard ideals whose reduced lexicographic
//!   Groebner bases are published and hand-checkable — the cyclic-3
//!   benchmark and the twisted cubic. The reduced basis is unique for a
//!   fixed monomial order, so these are reference *outputs*.
//! * **Structural re-derivation.** Buchberger's criterion, ideal
//!   membership of every input generator, reducedness, and idempotence,
//!   all computed from the output basis alone, under all three monomial
//!   orders. A negative control confirms the basis is not deciding
//!   everything.

use dac_out_of_family::algebra::buchberger::{
    in_ideal, is_reduced_basis, normal_form, satisfies_buchberger_criterion,
};
use dac_out_of_family::{reduced_groebner_basis, Monomial, MonomialOrder, Poly, Rat};

const XYZ: [&str; 3] = ["x", "y", "z"];
const MAX_ROUNDS: usize = 10_000;

/// A polynomial in three variables from integer-coefficient terms.
fn poly(order: MonomialOrder, terms: &[([u32; 3], i128)]) -> Poly {
    Poly::from_terms(
        3,
        order,
        terms
            .iter()
            .map(|(e, c)| (Monomial::new(e.to_vec()), Rat::int(*c)))
            .collect(),
    )
}

fn shown(basis: &[Poly]) -> Vec<String> {
    basis.iter().map(|p| p.show(&XYZ)).collect()
}

/// Cyclic-3: the elementary symmetric relations e1 = 0, e2 = 0, e3 = 1.
fn cyclic3(order: MonomialOrder) -> Vec<Poly> {
    vec![
        poly(order, &[([1, 0, 0], 1), ([0, 1, 0], 1), ([0, 0, 1], 1)]),
        poly(order, &[([1, 1, 0], 1), ([0, 1, 1], 1), ([1, 0, 1], 1)]),
        poly(order, &[([1, 1, 1], 1), ([0, 0, 0], -1)]),
    ]
}

/// The twisted cubic {(t, t^2, t^3)}: the ideal <x^2 - y, x^3 - z>.
fn twisted_cubic(order: MonomialOrder) -> Vec<Poly> {
    vec![
        poly(order, &[([2, 0, 0], 1), ([0, 1, 0], -1)]),
        poly(order, &[([3, 0, 0], 1), ([0, 0, 1], -1)]),
    ]
}

fn basis_of(input: &[Poly]) -> Vec<Poly> {
    reduced_groebner_basis(input, MAX_ROUNDS).expect("basis within the round limit")
}

// --- literature anchors ----------------------------------------------

#[test]
fn cyclic3_reproduces_its_published_lex_basis() {
    let g = basis_of(&cyclic3(MonomialOrder::Lex));
    assert_eq!(
        shown(&g),
        vec![
            "x + y + z".to_string(),
            "y^2 + y*z + z^2".to_string(),
            "z^3 - 1".to_string(),
        ]
    );
}

#[test]
fn twisted_cubic_reproduces_its_published_lex_basis() {
    let g = basis_of(&twisted_cubic(MonomialOrder::Lex));
    assert_eq!(
        shown(&g),
        vec![
            "x^2 - y".to_string(),
            "x*y - z".to_string(),
            "x*z - y^2".to_string(),
            "y^3 - z^2".to_string(),
        ]
    );
}

// --- structural re-derivation, all three orders ----------------------

#[test]
fn every_basis_satisfies_buchbergers_criterion_and_generates_its_ideal() {
    for order in [
        MonomialOrder::Lex,
        MonomialOrder::GrLex,
        MonomialOrder::GrevLex,
    ] {
        for input in [cyclic3(order), twisted_cubic(order)] {
            let g = basis_of(&input);
            assert!(
                satisfies_buchberger_criterion(&g),
                "criterion failed for {order:?}: {:?}",
                shown(&g)
            );
            assert!(
                is_reduced_basis(&g),
                "not reduced for {order:?}: {:?}",
                shown(&g)
            );
            for f in &input {
                assert!(
                    in_ideal(&g, f),
                    "generator {} not in the ideal under {order:?}",
                    f.show(&XYZ)
                );
            }
        }
    }
}

#[test]
fn the_reduced_basis_is_a_fixed_point() {
    // The reduced basis is unique for a fixed order, so recomputing from
    // it must return it unchanged.
    for order in [
        MonomialOrder::Lex,
        MonomialOrder::GrLex,
        MonomialOrder::GrevLex,
    ] {
        for input in [cyclic3(order), twisted_cubic(order)] {
            let g = basis_of(&input);
            assert_eq!(shown(&basis_of(&g)), shown(&g), "not idempotent: {order:?}");
        }
    }
}

#[test]
fn membership_is_decided_for_derived_elements() {
    let order = MonomialOrder::Lex;
    let g = basis_of(&cyclic3(order));
    // z * (x + y + z) is in the ideal by construction.
    let f = poly(order, &[([1, 0, 1], 1), ([0, 1, 1], 1), ([0, 0, 2], 1)]);
    assert!(in_ideal(&g, &f));
    // So is the difference of two generators.
    let gens = cyclic3(order);
    assert!(in_ideal(&g, &gens[0].sub(&gens[1])));
}

#[test]
fn a_non_member_is_not_decided() {
    // Negative control: z is not in the cyclic-3 ideal (the ideal is
    // proper, and z is a unit modulo it: z^3 = 1). Its normal form must
    // be non-zero, otherwise the membership checks above would pass for
    // a basis that collapses everything.
    let order = MonomialOrder::Lex;
    let g = basis_of(&cyclic3(order));
    let z = poly(order, &[([0, 0, 1], 1)]);
    assert!(!in_ideal(&g, &z));
    assert_eq!(normal_form(&z, &g).show(&XYZ), "z");
}

#[test]
fn the_monomial_order_changes_the_answer() {
    // The order is a parameter every pass consumes, not a formality: the
    // same ideal has different reduced bases under different orders.
    let lex = shown(&basis_of(&cyclic3(MonomialOrder::Lex)));
    let grlex = shown(&basis_of(&cyclic3(MonomialOrder::GrLex)));
    let grevlex = shown(&basis_of(&cyclic3(MonomialOrder::GrevLex)));
    assert_eq!(grlex, grevlex, "grlex and grevlex agree on this ideal");
    assert_ne!(lex, grlex, "lex should differ from the graded orders here");
}
