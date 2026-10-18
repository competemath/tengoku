/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ThirdChordAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `𝔪`-membership of the chord/Vieta data and non-vanishing of the denominator (issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  For parameters `z₁, z₂ ∈ 𝔪` the formal-side addition law
(`Reduction/FormalGroupAdditivity.lean`) produces the numeric chord slope `λ = chordSlope`, the
intercept `ν = chordIntercept`, the Vieta third root `t = thirdRootNum`, and the third-chord
`w`-value `w₃ = thirdChordW = λ t + ν`.  Each of these is `adicEvalMv 𝔪 ![z₁, z₂]` of a formal
series with vanishing constant coefficient, so each lands in the maximal ideal `𝔪`.

The load-bearing consequence is that the **negation denominator**
`den = adicEvalMv 𝔪 ![z₁, z₂] formalGroupDen = 1 − a₁ t − a₃ w₃`
is congruent to `1` modulo `𝔪`, hence a unit and in particular **nonzero**.  This discharges the
`den ≠ 0` (`hden`) hypothesis of `WeierstrassCurve.localParam_add_secant` /
`WeierstrassCurve.localParam_add_of_X_ne` (`Reduction/ThirdChordAffine.lean`), one of the four
non-degeneracy side conditions of the secant additivity identity of #367.

⚠️ This paragraph used to close *"(The remaining `w₃ ≠ 0` / `X₃ ∉ {x₁, x₂}` conditions, the doubling
case #373, and the inverse case remain for the full `E₁(K)` subgroup closure.)"*  **All four are
merged**, and one of them not by being discharged but by being *removed*:

* `w₃ ≠ 0` — `WeierstrassCurve.thirdChordW_ne_zero` (`Reduction/ThirdChordNonvanishing.lean`);
* `X₃ ∉ {x₁, x₂}` — ⚠️ **eliminated, not discharged**:
  `WeierstrassCurve.addX_eq_thirdChordX_of_secant` (`Reduction/ThirdChordAffineUncond.lean`, #376)
  proves `addX = X₃` as a `(z, w)`-level field
  identity, so the hypothesis never arises; see `WeierstrassCurve.localParam_add_of_X_ne_uncond`;
* the doubling case — `WeierstrassCurve.thirdChordPoint_functional_eq_diag`
  (`Reduction/FormalGroupTangent.lean`, #373) and `localParam_add_of_X_eq_uncond`;
* the inverse case — `WeierstrassCurve.adicEvalMv_formalGroupZW_eq_zero_of_X_eq`
  (`Reduction/InverseAdditivity.lean`), unconditional at `2`-torsion via
  `zParamHatEquiv_neg_uncond` (`Reduction/KernelNegationUncond.lean`, #377);
* and the subgroup closure itself is `WeierstrassCurve.reducesToZero_add` / `E₁`
  (`Reduction/KernelAddClosure.lean`).

## Main results

* `WeierstrassCurve.chordSlope_mem`, `chordIntercept_mem`, `thirdRootNum_mem`, `thirdChordW_mem` —
  the chord/Vieta data all lie in `𝔪`.
* `WeierstrassCurve.adicEvalMv_formalGroupDen_ne_zero` — `den ≠ 0` (it is `≡ 1 mod 𝔪`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open MvPowerSeries IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

/-! ### Vanishing constant coefficients of the chord/Vieta series

These are proved privately in `FormalGroup/GenuineLaw.lean`; following the pattern of
`Reduction/FormalGroupEval.lean` we re-derive the ones needed here so this file stays
self-contained. -/

section ConstantCoeff

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private lemma cc_formalWDividedDiff : MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
    (le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff)

private lemma cc_formalGroupNu : MvPowerSeries.constantCoeff W.formalGroupNu = 0 := by
  rw [formalGroupNu, map_sub, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, sub_zero,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := PowerSeries.coeff_toMvPowerSeries_single W.formalW (0 : Fin 2) 0
  rw [Finsupp.single_zero] at h
  rw [h]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)

private lemma cc_formalGroupSub : MvPowerSeries.constantCoeff W.formalGroupSub = 0 := by
  rw [formalGroupSub]
  simp [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C,
    W.cc_formalWDividedDiff, W.cc_formalGroupNu]

private lemma cc_formalThirdRoot : MvPowerSeries.constantCoeff W.formalThirdRoot = 0 := by
  rw [formalThirdRoot]
  simp [map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X, W.cc_formalGroupSub]

end ConstantCoeff

/-! ### `𝔪`-membership of the numeric chord/Vieta data -/

section Membership

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
variable (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)

omit [IsFractionRing R K]

/-- The numeric chord slope `λ = chordSlope` lies in `𝔪` (`formalWDividedDiff` has zero constant
coefficient). -/
theorem chordSlope_mem : chordSlope R W ha ∈ (maximalIdeal R).asIdeal := by
  rw [chordSlope]
  exact adicEvalMv_mem _ ha (integralModel R W).cc_formalWDividedDiff

/-- The numeric chord intercept `ν = chordIntercept` lies in `𝔪` (`formalGroupNu` has zero constant
coefficient). -/
theorem chordIntercept_mem : chordIntercept R W ha ∈ (maximalIdeal R).asIdeal := by
  rw [chordIntercept]
  exact adicEvalMv_mem _ ha (integralModel R W).cc_formalGroupNu

/-- The numeric Vieta third root `t = thirdRootNum` lies in `𝔪` (`formalThirdRoot` has zero constant
coefficient). -/
theorem thirdRootNum_mem : thirdRootNum R W ha ∈ (maximalIdeal R).asIdeal := by
  rw [thirdRootNum]
  exact adicEvalMv_mem _ ha (integralModel R W).cc_formalThirdRoot

/-- The third-chord `w`-value `w₃ = thirdChordW = λ t + ν` lies in `𝔪`. -/
theorem thirdChordW_mem : thirdChordW R W ha ∈ (maximalIdeal R).asIdeal := by
  rw [thirdChordW]
  exact (maximalIdeal R).asIdeal.add_mem
    ((maximalIdeal R).asIdeal.mul_mem_left _ (thirdRootNum_mem R W ha))
    (chordIntercept_mem R W ha)

/-- **The negation denominator is nonzero.**  With `t = thirdRootNum`, `w₃ = thirdChordW`, the
numeric denominator `den = adicEvalMv 𝔪 ![z₁, z₂] formalGroupDen = 1 − a₁ t − a₃ w₃` satisfies
`1 − den ∈ 𝔪` (both `t` and `w₃` lie in `𝔪`), so `den ≡ 1 mod 𝔪`; if `den` were `0` then `1 ∈ 𝔪`,
contradicting that `𝔪` is a proper (prime) ideal.  This discharges the `hden` hypothesis of
`localParam_add_secant` / `localParam_add_of_X_ne`. -/
theorem adicEvalMv_formalGroupDen_ne_zero :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen ≠ 0 := by
  intro h0
  have hmem : (1 : R)
      - adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen
        ∈ (maximalIdeal R).asIdeal := by
    rw [adicEvalMv_formalGroupDen]
    have hrw : (1 : R)
        - (1 - (integralModel R W).a₁ * thirdRootNum R W ha
            - (integralModel R W).a₃
              * (chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha))
        = (integralModel R W).a₁ * thirdRootNum R W ha
          + (integralModel R W).a₃
              * (chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha) := by ring
    rw [hrw]
    refine (maximalIdeal R).asIdeal.add_mem
      ((maximalIdeal R).asIdeal.mul_mem_left _ (thirdRootNum_mem R W ha))
      ((maximalIdeal R).asIdeal.mul_mem_left _ ?_)
    exact (maximalIdeal R).asIdeal.add_mem
      ((maximalIdeal R).asIdeal.mul_mem_left _ (thirdRootNum_mem R W ha))
      (chordIntercept_mem R W ha)
  rw [h0, sub_zero] at hmem
  exact (maximalIdeal R).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)

end Membership

end WeierstrassCurve
