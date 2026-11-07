/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Tengoku.Seed.FieldTheory.Separable
public import Tengoku.Seed.RingTheory.Polynomial.GaussLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial roots over a fraction field

Separability for a polynomial over a domain is stronger than separability after passage to its
fraction field. The latter is the relevant condition for function-field factorization in BCHKS25.
These lemmas keep that passage explicit. They also isolate the rational root of a linear factor;
they do not assert that this rational root is a polynomial or bound its degrees.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

@[expose] public section

namespace Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- For a factor irreducible over the fraction field, separability is exactly nonvanishing of
the original derivative. No perfectness or characteristic restriction is needed.-/
theorem separable_map_fractionField_iff {p : R[X]}
    (hp : Irreducible (p.map (algebraMap R K))) :
    (p.map (algebraMap R K)).Separable ↔ p.derivative ≠ 0 := by
  rw [separable_iff_derivative_ne_zero hp, derivative_map]
  exact not_congr (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K))

/-- A primitive irreducible factor is separable over the fraction field precisely when its
derivative is nonzero. Primitivity explicitly excludes nonunit constant content factors.-/
theorem IsPrimitive.separable_map_fractionField_iff [IsGCDMonoid R] {p : R[X]}
    (hprim : p.IsPrimitive) (hp : Irreducible p) :
    (p.map (algebraMap R K)).Separable ↔ p.derivative ≠ 0 := by
  exact Polynomial.separable_map_fractionField_iff
    ((hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hp)

end Polynomial
