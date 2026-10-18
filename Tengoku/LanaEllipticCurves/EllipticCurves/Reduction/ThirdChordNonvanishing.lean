/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.AdditivityValuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Non-vanishing of the third chord point (`w₃ ≠ 0`, issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  For two parameters `z₁, z₂ ∈ 𝔪` with `z₁ ≠ z₂` the formal-side
addition law produces the third chord point `(t, w₃)` in the `(z, w)`-plane, with `t = thirdRootNum`
the Vieta third root and `w₃ = thirdChordW = λ t + ν`.

The secant coordinate identity `localParam_add_secant` / the point-level `localParam_add_of_X_ne`
(`Reduction/ThirdChordAffine.lean`) carry a hypothesis `hw : w₃ ≠ 0` (geometrically: the third
chord point is not at infinity, i.e. `P + Q ≠ O`).  This file **discharges** it in the secant case,
so — together with the `hden : den ≠ 0` discharge (`Reduction/AdditivityValuation.lean`) — two of
the four non-degeneracy side conditions of `localParam_add_of_X_ne` are discharged.

⚠️ **That count is a tally, and it has since decayed: the other two are gone as well.**  This
sentence closed *"two of the four non-degeneracy side conditions of the secant additivity are now
unconditional"*, which is still true of `localParam_add_of_X_ne` itself and no longer describes the
front.  The distinctness pair `hd1, hd2` was **removed rather than discharged** — #376's
`addX_eq_thirdChordX_of_secant` (`EllipticCurves.Reduction.ThirdChordAffineUncond`) proves
`addX = X₃` as a `(z, w)`-level symmetric-function field identity that never mentions `X₃`'s
distinctness, and `localParam_add_of_X_ne_uncond`
(`EllipticCurves.Reduction.AdditivityUncond`) is the secant additivity with all four side
conditions gone.  `EllipticCurves.Reduction.SecantAdditivity`, which consumes this file, records
the same thing.  **State the position, not a tally.**

The key observation is that `(t, w₃)` solves the same numeric Weierstrass functional equation as the
coordinate expansion `wParam`, and both `t, w₃` lie in `𝔪`; by uniqueness of the small solution
(`wFunctionalEq_unique`) one has `w₃ = wParam t`.  This turns `w₃ ≠ 0` into `t ≠ 0` (as
`wParam z = z³ · unit`).  Finally `t = 0` would force `w₃ = λ·0 + ν = ν = 0`, contradicting
`chordIntercept_ne_zero_secant` (`ν ≠ 0` in the secant case) — so `t ≠ 0`, whence `w₃ ≠ 0`.

## Main results

* `WeierstrassCurve.thirdChordW_eq_wParam` — `w₃ = wParam t` (the third chord `w`-value is the small
  solution of the functional equation at `t`).
* `WeierstrassCurve.thirdRootNum_ne_zero` — `t ≠ 0` in the secant case.
* `WeierstrassCurve.thirdChordW_ne_zero` — **`w₃ ≠ 0`** in the secant case (discharges `hw`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
variable (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)

/-- **The third chord `w`-value is the coordinate expansion `wParam t`.**  Both `thirdChordW` (the
`(z, w)`-plane value of the chord line at the Vieta third root `t`) and `wParam t` solve the numeric
Weierstrass functional equation with parameter `t = thirdRootNum` and lie in `𝔪`; by uniqueness of
the small solution (`wFunctionalEq_unique`) they coincide.  Requires `z₁ ≠ z₂` (the secant case,
where `(t, w₃)` is on the curve). -/
theorem thirdChordW_eq_wParam (hz : z₁ ≠ z₂) :
    thirdChordW R W ha = wParam R W (thirdRootNum_mem R W ha) := by
  refine IsFractionRing.injective R K ?_
  have hZlt : valuation K (maximalIdeal R) (algebraMap R K (thirdRootNum R W ha)) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr (thirdRootNum_mem R W ha)
  have hW1lt : valuation K (maximalIdeal R) (algebraMap R K (thirdChordW R W ha)) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr (thirdChordW_mem R W ha)
  have hwm : wParam R W (thirdRootNum_mem R W ha) ∈ (maximalIdeal R).asIdeal := by
    rw [wParam_eq_cube_mul]
    exact Ideal.mul_mem_right _ _
      (by rw [pow_succ, pow_two]; exact Ideal.mul_mem_left _ _ (thirdRootNum_mem R W ha))
  have hW2lt : valuation K (maximalIdeal R)
      (algebraMap R K (wParam R W (thirdRootNum_mem R W ha))) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr hwm
  refine wFunctionalEq_unique R W hZlt hW1lt hW2lt ?_ ?_
  · have h := congrArg (algebraMap R K) (thirdChord_functional_eq R W ha hz)
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h
  · have h := congrArg (algebraMap R K) (wParam_functional_eq R W (thirdRootNum_mem R W ha))
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h

variable (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal) (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal)
  (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0) (hx : xParam R W hz₁ ≠ xParam R W hz₂)

include hz₁ hz₂ hz₁0 hz₂0 hx in
/-- **The Vieta third root is nonzero (secant case).**  If `t = thirdRootNum = 0` then
`w₃ = λ·0 + ν = ν`, while `w₃ = wParam 0 = 0³ · unit = 0`; so `ν = 0`, contradicting
`chordIntercept_ne_zero_secant`.  Geometrically: `t = 0` would place the third chord point at the
origin (`P + Q = O`), impossible when the chord is a genuine secant (`xParam z₁ ≠ xParam z₂`). -/
theorem thirdRootNum_ne_zero : thirdRootNum R W ha ≠ 0 := by
  intro ht0
  have hz : z₁ ≠ z₂ := fun h => hx (by subst h; rfl)
  have hν : chordIntercept R W ha ≠ 0 := fun hc =>
    chordIntercept_ne_zero_secant R W ha hz₁ hz₂ hz₁0 hz₂0 hx (by rw [hc, map_zero])
  have h1 : thirdChordW R W ha = chordIntercept R W ha := by
    rw [thirdChordW, ht0, mul_zero, zero_add]
  have h2 : thirdChordW R W ha = wParam R W (thirdRootNum_mem R W ha) :=
    thirdChordW_eq_wParam R W ha hz
  have h3 : wParam R W (thirdRootNum_mem R W ha) = 0 := by
    rw [wParam_eq_cube_mul]
    exact mul_eq_zero_of_left (by rw [ht0]; ring) _
  rw [h2, h3] at h1
  exact hν h1.symm

include hz₁ hz₂ hz₁0 hz₂0 hx in
/-- **The third chord point is not at infinity (`w₃ ≠ 0`, secant case).**  Since `w₃ = wParam t`
(`thirdChordW_eq_wParam`) and `t ≠ 0` (`thirdRootNum_ne_zero`), the factorisation
`wParam t = t³ · unit` gives `w₃ ≠ 0`.  This discharges the `hw` hypothesis of the secant
coordinate additivity `localParam_add_secant` / `localParam_add_of_X_ne`. -/
theorem thirdChordW_ne_zero : thirdChordW R W ha ≠ 0 := by
  rw [thirdChordW_eq_wParam R W ha (fun h => hx (by subst h; rfl))]
  exact wParam_ne_zero R W _ (thirdRootNum_ne_zero R W ha hz₁ hz₂ hz₁0 hz₂0 hx)

end WeierstrassCurve
