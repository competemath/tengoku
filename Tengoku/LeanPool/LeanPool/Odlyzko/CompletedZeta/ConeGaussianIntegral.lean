/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FundamentalConeSeries
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.UnitAveragedGaussian

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory NumberField NumberField.Units
  NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

/-- An ideal set element used in the Odlyzko-bound argument. -/
noncomputable def idealSetElement
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : K :=
  (preimageOfMemIntegerSet (idealSetEquiv K J a).val : 𝓞 K)

/--
@isnad1 id=ne.0h3v.s9.59b0effedc91 from=translated src=- shape=f428aec0 vocab=4d8776d4
-/
theorem idealSetElement_ne_zero
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    idealSetElement K J a ≠ 0 := by
  rw [idealSetElement]
  simp

/--
@isnad1 id=eq.0h3v.s9.4c8f9171aa96 from=translated src=- shape=3e740084 vocab=b53fc0a7
-/
theorem absNorm_idealSetElement
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    (((|Algebra.norm ℚ (idealSetElement K J a)| : ℚ) : ℝ)) =
      idealSetIntNorm K J a := by
  calc
    (((|Algebra.norm ℚ (idealSetElement K J a)| : ℚ) : ℝ)) =
        mixedEmbedding.norm (mixedEmbedding K (idealSetElement K J a)) := by simp
    _ = mixedEmbedding.norm (a : mixedSpace K) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]
    _ = idealSetIntNorm K J a := by
      rw [idealSetIntNorm, intNorm_idealSetEquiv_apply]

variable [IsTotallyComplex K]

/--
@isnad1 id=eq.1h4v.s9.f1a0a71b32cc from=translated src=- shape=46800fb7 vocab=bd6382f7
-/
theorem integral_idealSet_complexPlaceMellinGaussian
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      complexPlaceMellinGaussian K (idealSetElement K J a) s q
      ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) =
      ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        (idealSetIntNorm K J a : ℂ) ^ (-s) := by
  rw [integral_complexPlaceMellinGaussian K
    (idealSetElement_ne_zero K J a) hs]
  congr 1
  congr 1
  exact_mod_cast absNorm_idealSetElement K J a

/--
@isnad1 id=hassum.1h3v.s9.16eb6510582f from=translated src=- shape=d69fb36e vocab=fe9fddd7
-/
theorem hasSum_integral_idealSet_complexPlaceMellinGaussian
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun a : idealSet K J ↦
        ∫ q : InfinitePlace K → ℝ,
          complexPlaceMellinGaussian K (idealSetElement K J a) s q
          ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0)))
      (((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        fundamentalConeZeta K J s) := by
  have h := (hasSum_idealSet_inverseNormPower K J hs).mul_left
    (((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K)
  refine h.congr_fun (fun a : idealSet K J ↦ ?_)
  exact integral_idealSet_complexPlaceMellinGaussian K J a
    (lt_trans zero_lt_one hs)

end NumberField.Odlyzko
