/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantMultiplicativeReductionBaseChange
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.PotentialGoodReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Potential multiplicative reduction forces `v_R(j) < 0` at the base (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be elliptic.  This file delivers the **ungated forward obstruction** of the
multiplicative half of Silverman AEC VII.5.5 in its quantified, base-landing form — the exact
multiplicative companion of the merged good-reduction brick
`WeierstrassCurve.isIntegral_j_of_hasGoodReduction_baseChange_over` (#504,
`Reduction/PotentialGoodReduction.lean`):

> If `W` acquires **multiplicative reduction over a discrete valuation subring `A ⊆ L`** of some
> field extension `L / K`, and `A` **lies over the base DVR `R`**, then the base valuation of the
> `j`-invariant is negative: `1 < v_R(W.j)` (multiplicative-valuation convention), equivalently
> `W.j` is **not integral at the base place**.

The sharp conclusion `1 < v_R(W.j)` is the base-place reflection of
`WeierstrassCurve.one_lt_valuation_j_of_hasMultiplicativeReduction` (`v(j) < 0` over a single DVR,
`Reduction/JInvariantMultiplicativeReduction.lean`), obtained from the per-extension core
`WeierstrassCurve.not_mem_j_of_hasMultiplicativeReduction_baseChange` (#505,
`Reduction/JInvariantMultiplicativeReductionBaseChange.lean`, only `algebraMap K L W.j ∉ A`) by
reflecting the extension-place non-membership back to the base valuation via the DVR converse
`WeierstrassCurve.exists_algebraMap_eq_of_valuation_le_one` (#504).

## Key points

* **"Lies over `R`".** The condition that the valuation subring `A ⊆ L` "lies over" the base is
  packaged as `∀ r : R, algebraMap K L (algebraMap R K r) ∈ A`, i.e. the base ring `R` maps into
  `A` through the tower `R → K → L` (`R ⊆ A ∩ K`).  This is the honest structural meaning of
  "lies over" and the mirror of #504's contraction bound `A ∩ K ⊆ R`.  It does **not** smuggle the
  theorem's content: the content — multiplicative reduction ⟹ `j ∉ A` — is #505.

* **The reflection.** If `v_R(W.j) ≤ 1` then by the DVR converse `W.j = algebraMap R K r` for some
  `r : R`, whence `algebraMap K L W.j ∈ A` by `hover r`, contradicting #505.  So `1 < v_R(W.j)`.

## Main results

* `WeierstrassCurve.one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over` — the sharp
  `∀`-form: multiplicative reduction of `W⁄L` over any DVR extension `A` lying over `R` forces
  `1 < v_R(W.j)`.
* `WeierstrassCurve.not_isIntegral_j_of_hasMultiplicativeReduction_baseChange_over` — the
  membership corollary: `¬ ∃ r : R, algebraMap R K r = W.j` (`W.j` not integral at the base place).
* `WeierstrassCurve.not_hasMultiplicativeReduction_baseChange_over_of_j_mem` — the contrapositive:
  a `j` integral at the base place rules out multiplicative reduction over any DVR extension lying
  over `R`.

## Scope

This delivers the **ungated forward obstruction**.  The **converse** (`v(j) < 0` ⟹ potential
multiplicative reduction) needs the Tate curve, absent from the repository and the pinned Mathlib,
and is left to a follow-on — exactly as for #504/#505.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1, VII.5.5.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (R) in
/-- **Potential multiplicative reduction ⟹ `v_R(j) < 0` (sharp `∀`-form).** If `W⁄L` has
multiplicative reduction over a discrete valuation subring `A ⊆ L` that **lies over** `R` (the base
ring maps into `A` through the tower `R → K → L`), then the base valuation of `W.j` is negative,
`1 < v_R(W.j)` in the multiplicative-valuation convention.  This is the base-place reflection of
`one_lt_valuation_j_of_hasMultiplicativeReduction`, obtained from the per-extension #505
`not_mem_j_of_hasMultiplicativeReduction_baseChange` via the DVR converse
`exists_algebraMap_eq_of_valuation_le_one` (#504). -/
theorem one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hover : ∀ r : R, algebraMap K L (algebraMap R K r) ∈ A)
    (W : WeierstrassCurve K) [W.IsElliptic] (h : HasMultiplicativeReduction A (W⁄L)) :
    1 < valuation K (maximalIdeal R) W.j := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_valuation_le_one R W.j hle
  exact not_mem_j_of_hasMultiplicativeReduction_baseChange A W h (hr ▸ hover r)

variable (R) in
/-- **Potential multiplicative reduction ⟹ `j` not integral at the base (membership form).**
Corollary of `one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over`: there is no
`r : R` with `algebraMap R K r = W.j`.  This is the base-landing multiplicative companion of
`isIntegral_j_of_hasGoodReduction_baseChange_over` (#504). -/
theorem not_isIntegral_j_of_hasMultiplicativeReduction_baseChange_over
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hover : ∀ r : R, algebraMap K L (algebraMap R K r) ∈ A)
    (W : WeierstrassCurve K) [W.IsElliptic] (h : HasMultiplicativeReduction A (W⁄L)) :
    ¬ ∃ r : R, algebraMap R K r = W.j := by
  rintro ⟨r, hr⟩
  have hv := one_lt_valuation_j_of_hasMultiplicativeReduction_baseChange_over R A hover W h
  rw [← hr] at hv
  exact absurd (valuation_le_one (maximalIdeal R) r) (not_le.2 hv)

variable (R) in
/-- **Contrapositive.** A `j`-invariant that *is* integral at the base place rules out
multiplicative reduction over *any* discrete valuation subring extension lying over `R`. -/
theorem not_hasMultiplicativeReduction_baseChange_over_of_j_mem
    {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (hover : ∀ r : R, algebraMap K L (algebraMap R K r) ∈ A)
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : ∃ r : R, algebraMap R K r = W.j) :
    ¬ HasMultiplicativeReduction A (W⁄L) :=
  fun h => not_isIntegral_j_of_hasMultiplicativeReduction_baseChange_over R A hover W h hj

end WeierstrassCurve
