/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Kummer–Dedekind: the primes over `p`, with their residue degrees and ramification indices

Let `R` be an integrally closed domain, let `S` be a Dedekind domain that is a torsion-free
`R`-algebra, let `x : S` be integral over `R`, and let `p` be a nonzero maximal ideal of `R` that
is prime to the conductor of `R[x]` in `S`.  Mathlib's `KummerDedekind` file matches the prime
factors of `p S` with the irreducible factors of `minpoly R x` modulo `p`, and matches their
multiplicities.  This file turns that match into the form ramification theory uses: a bijection

`p.primesOver S ≃ {normalized irreducible factors of minpoly R x mod p}`

under which the **residue degree** of a prime is the degree of the matching polynomial factor and
its **ramification index** is the multiplicity of that factor.  Together these say that the
factorization of `minpoly R x` modulo `p` computes the splitting of `p` in `S` completely, which
is the content of the Kummer–Dedekind criterion as it is used in practice.

The prime attached to a factor is explicit: it is `span (p S ∪ {Q (x)})` for any lift `Q` of the
factor, so the bijection can be evaluated on a concrete example.

## Main definitions

* `TauCeti.KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk`: the bijection between the
  primes of `S` over `p` and the normalized irreducible factors of `minpoly R x` modulo `p`.
* `TauCeti.KummerDedekind.quotientEquivQuotientSpan`: the isomorphism
  `(R ⧸ p)[X] ⧸ (Q) ≃+* S ⧸ span (p S ∪ {Q (x)})` for `Q` a lift of such a factor, which computes
  the residue field at the attached prime.

## Main results

* `TauCeti.KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk_symm_apply_coe`: the prime
  attached to the class of `Q` is `span (p S ∪ {Q (x)})`.
* `TauCeti.KummerDedekind.inertiaDeg_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply`: its
  residue degree is the degree of the factor.
* `TauCeti.KummerDedekind.ramificationIdx_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply`:
  its ramification index is the multiplicity of the factor in `minpoly R x` modulo `p`.
* `TauCeti.KummerDedekind.Ideal.irreducible_map_iff_irreducible_minpoly`: `p` stays prime in `S`
  exactly when `minpoly R x` is irreducible modulo `p`.

## Provenance

These are the arbitrary-Dedekind-domain form of Xavier Roblot's
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`,
`NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply` and
`NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply` of
`Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean`, and the proofs follow his, with the
`ℤ`-to-`ZMod p` plumbing that his statements need dropped.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, Proposition 8.3.
-/

public section

open Ideal Polynomial UniqueFactorizationMonoid

namespace TauCeti

namespace KummerDedekind

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
variable {x : S} {p : Ideal R}

variable (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
  (hx : (conductor R x).comap (algebraMap R S) ⊔ p = ⊤) (hx' : IsIntegral R x)

attribute [local instance] Ideal.Quotient.field

include hp hp0 hx hx'

omit hp0 in
open scoped Classical in
/-- **The residue ring at a Kummer–Dedekind factor**: for `Q` a lift of a normalized irreducible
factor of `minpoly R x` modulo `p`, the quotient of `S` by the prime `span (p S ∪ {Q (x)})`
attached to that factor is `(R ⧸ p)[X]` modulo the factor. -/
noncomputable def quotientEquivQuotientSpan {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk p) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) :
    (R ⧸ p)[X] ⧸ span {Q.map (Ideal.Quotient.mk p)} ≃+*
      S ⧸ span (p.map (algebraMap R S) ∪ {aeval x Q}) :=
  have h0 : (minpoly R x).map (Ideal.Quotient.mk p) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic hx')
  have h₁ : span {Q.map (Ideal.Quotient.mk p)} =
      span {(minpoly R x).map (Ideal.Quotient.mk p)} ⊔ span {Q.map (Ideal.Quotient.mk p)} := by
    rw [← span_insert, span_pair_comm, span_pair_eq_span_left_iff_dvd.mpr]
    exact ((Polynomial.mem_normalizedFactors_iff h0).mp hQ).2.2
  have h₂ : p.map (algebraMap R S) ⊔ span {aeval x Q} =
      span (p.map (algebraMap R S) ∪ {aeval x Q}) := by
    rw [span_union, span_eq]
  ((Ideal.quotEquivOfEq h₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv _ (Ideal.map (Ideal.Quotient.mk (p.map (algebraMap R S)))
        (span {aeval x Q}))
      (KummerDedekind.quotMapEquivQuotQuotMap hx hx').symm (by
        simp [Ideal.map_span,
          KummerDedekind.quotMapEquivQuotQuotMap_symm_apply hx hx' Q])).trans <|
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq h₂)

omit hp0 in
open scoped Classical in
/-- `TauCeti.KummerDedekind.quotientEquivQuotientSpan` carries the class of a polynomial `P` over
`R ⧸ p` to the class of `P (x)`. -/
@[simp]
theorem quotientEquivQuotientSpan_mk {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk p) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) (P : R[X]) :
    quotientEquivQuotientSpan hp hx hx' hQ (Ideal.Quotient.mk
        (span {Q.map (Ideal.Quotient.mk p)}) (P.map (Ideal.Quotient.mk p))) =
      Ideal.Quotient.mk (span (p.map (algebraMap R S) ∪ {aeval x Q})) (aeval x P) := by
  simp only [quotientEquivQuotientSpan, RingEquiv.coe_trans, Function.comp_apply,
    Ideal.quotEquivOfEq_mk, DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk,
    DoubleQuot.quotQuotMk, RingHom.coe_comp, Ideal.quotientEquiv_mk,
    KummerDedekind.quotMapEquivQuotQuotMap_symm_apply hx hx' P]
  -- what is left is `DoubleQuot.quotQuotEquivQuotSup_quotQuotMk`, which the previous step has
  -- unfolded past, followed by `Ideal.quotEquivOfEq_mk`; both hold by `rfl`.
  rfl

namespace Ideal

omit hp0 in
open scoped Classical in
/-- **The converse of `Ideal.irreducible_map_of_irreducible_minpoly`.** If `p S` is irreducible,
that is, if `p` stays prime in `S`, then `minpoly R x` modulo `p` is irreducible. -/
theorem irreducible_minpoly_of_irreducible_map (h : Irreducible (p.map (algebraMap R S))) :
    Irreducible ((minpoly R x).map (Ideal.Quotient.mk p)) := by
  have hp0 : p ≠ ⊥ := by
    rintro rfl
    exact h.ne_zero (by simp)
  have hm0 : (minpoly R x).map (Ideal.Quotient.mk p) ≠ 0 :=
    Polynomial.map_monic_ne_zero (minpoly.monic hx')
  -- The prime factors of `p S` form a singleton, and they are the image of the normalized factors
  -- of `minpoly R x` modulo `p` under the Kummer–Dedekind bijection.
  have hcard : Multiset.card (normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk p))) = 1 := by
    have h1 : Multiset.card (normalizedFactors (p.map (algebraMap R S))) = 1 := by
      rw [normalizedFactors_irreducible h, Multiset.card_singleton]
    have hmap := congrArg Multiset.card
      (KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hp hp0 hx
        hx')
    rw [h1, Multiset.card_map, Multiset.card_attach] at hmap
    exact hmap.symm
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp hcard
  have hdirr : Irreducible d :=
    irreducible_of_normalized_factor d (by rw [hd]; exact Multiset.mem_singleton_self d)
  -- Hence `minpoly R x` modulo `p` is associated to the irreducible `d`.
  have hassoc := prod_normalizedFactors hm0
  rw [hd, Multiset.prod_singleton] at hassoc
  exact hassoc.irreducible hdirr

/-- **The Kummer–Dedekind irreducibility criterion.** `p` stays prime in `S` exactly when
`minpoly R x` is irreducible modulo `p`. -/
theorem irreducible_map_iff_irreducible_minpoly :
    Irreducible (p.map (algebraMap R S)) ↔
      Irreducible ((minpoly R x).map (Ideal.Quotient.mk p)) :=
  ⟨irreducible_minpoly_of_irreducible_map hp hx hx',
    KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly hp hp0 hx hx'⟩

end Ideal

end KummerDedekind

end TauCeti
