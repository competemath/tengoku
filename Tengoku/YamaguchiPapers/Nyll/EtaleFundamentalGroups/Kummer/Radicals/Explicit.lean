/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The explicit one-component Kummer algebra

This file records the first concrete algebra facts for the Kummer equation
`X ^ n - a`.  After the boundary parameter has been inverted, its adjoined
root is a unit.  Consequently the derivative at that root is a unit exactly
when the exponent is a unit in the localized base ring.

No etaleness or derivative-unit conclusion is assumed here.  The remaining
geometric input is a producer that turns etaleness of the explicit Kummer
algebra into the derivative-unit side of the final equivalence.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v

/-- The defining equation of `AdjoinRoot (X ^ n - C a)`, over any commutative ring.
@isnad1 id=eq.0h3v.s12.5db2cc2e4db2 from=translated src=- shape=ab2a94b1 vocab=d6e514c7
-/
theorem adjoinRoot_root_pow
    {A : Type u} [CommRing A] (n : ℕ) (a : A) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n =
      AdjoinRoot.of (X ^ n - C a) a := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]

/-- A root of `X ^ n - a` is a unit when `a` is a unit and `n` is positive.
@isnad1 id=isunit.2h3v.s10.5d9cdbb04de5 from=translated src=- shape=208e0e47 vocab=e7ac5bff
-/
theorem isUnit_adjoinRoot_root_of_isUnit
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n) {a : A}
    (ha : IsUnit a) :
    IsUnit (AdjoinRoot.root (X ^ n - C a)) := by
  refine (isUnit_pow_iff hn.ne').mp ?_
  rw [adjoinRoot_root_pow]
  exact ha.map (AdjoinRoot.of (X ^ n - C a))

/-- Evaluation of the derivative of the explicit Kummer polynomial at its adjoined root.
@isnad1 id=eq.0h3v.s13.25c8e52b6d05 from=translated src=- shape=17a60d7a vocab=8f92708c
-/
theorem aeval_derivative_X_pow_sub_C
    {A : Type u} [CommRing A] (n : ℕ) (a : A) :
    aeval (AdjoinRoot.root (X ^ n - C a)) (X ^ n - C a).derivative =
      algebraMap A (AdjoinRoot (X ^ n - C a)) (n : A) *
        AdjoinRoot.root (X ^ n - C a) ^ (n - 1) := by
  simp [Polynomial.derivative_X_pow]

/--
The positive-degree monic Kummer algebra is faithfully flat over a nontrivial
base ring.

Indeed the monic quotient is free.  Positive degree makes it nontrivial over
a nontrivial base, hence free-module faithful flatness applies.
@isnad1 id=faithful.1h3v.s10.89777ac21b96 from=translated src=- shape=af04229c vocab=cb9efa29
-/
theorem faithfullyFlat_adjoinRoot_X_pow_sub_C
    {A : Type u} [CommRing A] [Nontrivial A] {n : ℕ} (hn : 0 < n)
    (a : A) :
    Module.FaithfullyFlat A (AdjoinRoot (X ^ n - C a)) := by
  let : Nontrivial (AdjoinRoot (X ^ n - C a)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      intro htop
      have h : IsUnit (X ^ n - C a) :=
        Ideal.span_singleton_eq_top.mp htop
      apply hn.ne'
      rw [← @Polynomial.natDegree_one A,
        ← (Polynomial.monic_X_pow_sub_C a hn.ne').eq_one_of_isUnit h,
        Polynomial.natDegree_X_pow_sub_C])
  let : Module.Free A (AdjoinRoot (X ^ n - C a)) :=
    (Polynomial.monic_X_pow_sub_C a hn.ne').free_adjoinRoot
  infer_instance

/--
The base ring detects units inside the positive-degree monic Kummer algebra.
@isnad1 id=iff.1h4v.s11.4deae4bd2d0e from=translated src=- shape=47a5b876 vocab=bd5f208f
-/
theorem isUnit_algebraMap_adjoinRoot_X_pow_sub_C_iff
    {A : Type u} [CommRing A] [Nontrivial A] {n : ℕ} (hn : 0 < n)
    (a b : A) :
    IsUnit (algebraMap A (AdjoinRoot (X ^ n - C a)) b) ↔ IsUnit b := by
  let : Module.FaithfullyFlat A (AdjoinRoot (X ^ n - C a)) :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hn a
  exact isUnit_map_iff (algebraMap A (AdjoinRoot (X ^ n - C a))) b

/--
For a Kummer polynomial with invertible constant term, its formal derivative at the
adjoined root is a unit exactly when the exponent is a unit in the base.
@isnad1 id=iff.2h3v.s12.380ae6a2f2ea from=translated src=- shape=78e9abe1 vocab=81bc5c2c
-/
theorem isUnit_aeval_derivative_iff_isUnit_natCast
    {A : Type u} [CommRing A] [Nontrivial A] {n : ℕ} (hn : 0 < n)
    {a : A} (ha : IsUnit a) :
    IsUnit (aeval (AdjoinRoot.root (X ^ n - C a))
      (X ^ n - C a).derivative) ↔ IsUnit (n : A) := by
  rw [aeval_derivative_X_pow_sub_C]
  constructor
  · intro h
    have hmap :
        IsUnit (algebraMap A (AdjoinRoot (X ^ n - C a)) (n : A)) :=
      ((Commute.all _ _).isUnit_mul_iff.mp h).1
    exact (isUnit_algebraMap_adjoinRoot_X_pow_sub_C_iff hn a (n : A)).mp hmap
  · intro h
    exact
      ((isUnit_algebraMap_adjoinRoot_X_pow_sub_C_iff hn a (n : A)).mpr h).mul
        ((isUnit_adjoinRoot_root_of_isUnit hn ha).pow (n - 1))

/--
On the complement of a prime boundary parameter `t`, derivative invertibility
for `X ^ n - t` is equivalent to invertibility of the localized exponent.

The right side is exactly the input consumed by the unit-descent lemma for
the map `R → R[1/t]`.
@isnad1 id=iff.2h4v.s12.2b19cf097dab from=translated src=- shape=2ef45d90 vocab=872ef168
-/
theorem isUnit_aeval_derivative_iff_isUnit_algebraMap_natCast_away
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] {t : R} [IsLocalization.Away t S]
    (ht : Prime t) {n : ℕ} (hn : 0 < n) :
    IsUnit (aeval
      (AdjoinRoot.root (X ^ n - C (algebraMap R S t)))
      (X ^ n - C (algebraMap R S t)).derivative) ↔
      IsUnit (algebraMap R S (n : R)) := by
  let : IsDomain S := IsLocalization.Away.isDomain S ht.ne_zero
  simpa using
    (isUnit_aeval_derivative_iff_isUnit_natCast
      (A := S) (a := algebraMap R S t) hn
      (IsLocalization.Away.algebraMap_isUnit t))

end EtaleFundamentalGroups.Kummer
