/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Good reduction is preserved under base change to a DVR extension (issue #393)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let `A` be a second
discrete valuation ring with fraction field `L = Frac A`, sitting over `R` (so we have compatible
scalar towers `R → A → L` and `R → K → L`; this is the situation of a finite extension `L / K` with
`A` the corresponding valuation ring). If a Weierstrass curve `W : WeierstrassCurve K` has good
reduction over `R`, then its base change `W⁄L : WeierstrassCurve L` has good reduction over `A`.

This is **rung C** of the Néron–Ogg–Shafarevich *good ⇒ unramified* ladder (Silverman AEC VII.7.1;
see `EllipticCurves/Reduction/ReductionGaloisEquivariant.lean`, issue #390 for rung A, and the
inertia-bridge issue #392 for rung B). Rung B produces the residue-trivial-torsion conclusion from a
good-reduction hypothesis *over `A`*; this file supplies exactly that hypothesis when `A` arises
from a finite extension.

## Key point

`HasGoodReduction R W` unfolds to `IsMinimal R W` together with
`valuation K (maximalIdeal R) W.Δ = 1`,
i.e. the discriminant of the integral minimal model `integralModel R W` is a **unit** in `R`. A ring
homomorphism sends units to units, so the discriminant stays a unit after base change to `A`; hence
`valuation L (maximalIdeal A) (W⁄L).Δ = 1`, and the base-changed integral model is automatically
minimal (its discriminant valuation already attains the top value `1`, which cannot be exceeded).
No hypothesis on the ramification of `A / R` is needed: good reduction is stable under *arbitrary*
base change. This is the formal reason good reduction is "good".

## Main results

* `WeierstrassCurve.isIntegral_baseChange` — `W⁄L` is integral over `A`.
* `WeierstrassCurve.valuation_Δ_baseChange_eq_one` — its discriminant has valuation `1` over `A`.
* `WeierstrassCurve.hasGoodReduction_baseChange` — `W⁄L` has good reduction over `A`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5, VII.7 Theorem 7.1.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R A K L : Type*}
variable [CommRing R] [CommRing A] [Field K] [Field L]
variable [Algebra R K] [Algebra A L] [Algebra R A] [Algebra K L] [Algebra R L]
variable [IsScalarTower R A L] [IsScalarTower R K L]

variable (R A) in
/-- The base change of the integral minimal model of `W` is an integral model of `W⁄L` over `A`:
`W⁄L = ((integralModel R W)⁄A)⁄L`. -/
theorem baseChange_integralModel_baseChange_eq (W : WeierstrassCurve K) [IsIntegral R W] :
    W⁄L = ((integralModel R W)⁄A)⁄L := by
  have hRAL : (algebraMap A L).comp (algebraMap R A) = algebraMap R L :=
    (IsScalarTower.algebraMap_eq R A L).symm
  have hRKL : (algebraMap K L).comp (algebraMap R K) = algebraMap R L :=
    (IsScalarTower.algebraMap_eq R K L).symm
  calc
    W⁄L = ((integralModel R W)⁄K)⁄L := by rw [baseChange_integralModel_eq R W]
    _ = (integralModel R W).map (algebraMap R L) := by simp only [baseChange, map_map, hRKL]
    _ = ((integralModel R W)⁄A)⁄L := by simp only [baseChange, map_map, hRAL]

variable (R A) in
/-- `W⁄L` is integral over `A` whenever `W` is integral over `R`. -/
theorem isIntegral_baseChange (W : WeierstrassCurve K) [IsIntegral R W] :
    IsIntegral A (W⁄L) :=
  ⟨(integralModel R W)⁄A, baseChange_integralModel_baseChange_eq R A W⟩

variable (R A) in
/-- The discriminant of `W⁄L` equals the base change to `A` of the discriminant of the integral
minimal model of `W`. -/
theorem Δ_baseChange_eq (W : WeierstrassCurve K) [IsIntegral R W] :
    (W⁄L).Δ = algebraMap A L (algebraMap R A (integralModel R W).Δ) := by
  rw [baseChange, map_Δ, ← integralModel_Δ_eq R W,
    ← IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R A L]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L]

variable (R) in
/-- If `W` has good reduction over `R`, the discriminant of its integral minimal model is a unit. -/
theorem isUnit_Δ_integralModel_of_hasGoodReduction (W : WeierstrassCurve K)
    [HasGoodReduction R W] : IsUnit (integralModel R W).Δ := by
  have h : valuation K (maximalIdeal R) (algebraMap R K (integralModel R W).Δ) = 1 := by
    rw [integralModel_Δ_eq R W]; exact HasGoodReduction.goodReduction
  rw [valuation_eq_one_iff_notMem] at h
  exact notMem_maximalIdeal.mp h

variable (R A) in
/-- **The discriminant of `W⁄L` has valuation `1` over `A`** when `W` has good reduction over `R`.
-/
theorem valuation_Δ_baseChange_eq_one (W : WeierstrassCurve K) [HasGoodReduction R W] :
    valuation L (maximalIdeal A) (W⁄L).Δ = 1 := by
  have hu : IsUnit (algebraMap R A (integralModel R W).Δ) :=
    (isUnit_Δ_integralModel_of_hasGoodReduction R W).map (algebraMap R A)
  rw [Δ_baseChange_eq R A W, valuation_eq_one_iff_notMem]
  exact notMem_maximalIdeal.mpr hu

variable (R A) in
/-- `W⁄L` is minimal over `A` when `W` has good reduction over `R`: its discriminant already has the
maximal possible valuation `1`, so no isomorphic integral model can do better. -/
theorem isMinimal_baseChange (W : WeierstrassCurve K) [HasGoodReduction R W] :
    IsMinimal A (W⁄L) := by
  haveI : IsIntegral A (W⁄L) := isIntegral_baseChange R A W
  haveI hone : IsIntegral A ((1 : VariableChange L) • (W⁄L)) := by rw [one_smul]; infer_instance
  refine ⟨⟨hone, ?_⟩⟩
  intro C _ _
  -- The discriminant of `1 • (W⁄L)` has the top valuation `1`, so every isomorphic integral model
  -- has smaller-or-equal discriminant valuation.
  change valuation_Δ_aux A (C • (W⁄L)) ≤ valuation_Δ_aux A ((1 : VariableChange L) • (W⁄L))
  rw [← Subtype.coe_le_coe,
    valuation_Δ_aux_eq_of_isIntegral A ((1 : VariableChange L) • (W⁄L)), one_smul,
    valuation_Δ_baseChange_eq_one R A W]
  exact (valuation_Δ_aux A (C • (W⁄L))).2

variable (R A) in
/-- **Good reduction is preserved under base change to a DVR extension.** If `W` has good reduction
over the DVR `R` (with `K = Frac R`), then its base change `W⁄L` has good reduction over any DVR `A`
lying over `R` with `L = Frac A`. -/
theorem hasGoodReduction_baseChange (W : WeierstrassCurve K) [HasGoodReduction R W] :
    HasGoodReduction A (W⁄L) where
  toIsMinimal := isMinimal_baseChange R A W
  goodReduction := valuation_Δ_baseChange_eq_one R A W

end WeierstrassCurve
