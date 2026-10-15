/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ConeGaussianRadial
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.IdealElementDecomposition
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.IdealThetaUnfolding
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory NumberField
  NumberField.InfinitePlace
open scoped ENNReal nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

open Classical in
private theorem integrable_tsum_of_summable_integral_norm
    {α E ι : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] [CompleteSpace E] [Countable ι]
    {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a ↦ ∑' i, F i a) μ := by
  let G : ι → α →₁[μ] E := fun i ↦ (hF_int i).toL1 (F i)
  have hnorm (i : ι) :
      ‖G i‖ = ∫ a, ‖F i a‖ ∂μ := by
    rw [show G i = (hF_int i).toL1 (F i) by grind,
      Integrable.norm_toL1, integral_norm_eq_lintegral_enorm
        (hF_int i).aestronglyMeasurable]
    simp only [edist_zero_right]
  have hG_norm : Summable fun i ↦ ‖G i‖ :=
    hF_sum.congr fun i ↦ (hnorm i).symm
  have hG_enorm : ∑' i, ‖G i‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hG_norm
  have hcoe :
      (⇑(∑' i, G i) : α → E) =ᵐ[μ]
        fun a ↦ ∑' i, F i a := by
    filter_upwards [Lp.coeFn_tsum hG_enorm,
      ae_all_iff.mpr (fun i ↦ (hF_int i).coeFn_toL1)] with a hsum hterm
    grind
  exact (L1.integrable_coeFn (∑' i, G i)).congr hcoe

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A complex place gaussian used in the Odlyzko-bound argument. -/
noncomputable def complexPlaceGaussian
    (x : K) (q : InfinitePlace K → ℝ) : ℂ :=
  Complex.exp
    (-((2 * Real.pi *
      ∑ w : InfinitePlace K, (w x) ^ 2 * (q w) ^ 2 : ℝ) : ℂ))

open Classical in
/--
@isnad1 id=eq.1h4v.s6.f84d06d985d2 from=translated src=- shape=5cb40bae vocab=5de69d3b
-/
theorem complexPlaceMellinGaussian_eq_prod_cpow_mul_gaussian
    (x : K) (s : ℂ) (q : InfinitePlace K → ℝ)
    (hq : ∀ w, 0 ≤ q w) :
    complexPlaceMellinGaussian K x s q =
      ((∏ w : InfinitePlace K, q w : ℝ) : ℂ) ^ (2 * s - 1) *
        complexPlaceGaussian K x q := by
  classical
  rw [complexPlaceMellinGaussian, complexPlaceGaussian,
    Finset.prod_mul_distrib,
    ← cpow_prod_of_nonneg Finset.univ q
      (fun w _ ↦ hq w) (2 * s - 1),
    ← Complex.exp_sum]
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  grind

variable [IsTotallyComplex K]

open Classical in
/--
@isnad1 id=eq.0h2v.s6.0adc63c76d8b from=translated src=- shape=39bb1ff9 vocab=c6d88654
-/
theorem prod_complexPlace_eq_prod_infinitePlace
    (f : InfinitePlace K → ℝ) :
    (∏ w : {w : InfinitePlace K // IsComplex w}, f w.1) =
      ∏ w : InfinitePlace K, f w := by
  classical
  symm
  simpa only using
    Finset.prod_subtype (Finset.univ : Finset (InfinitePlace K))
      (fun w ↦ by simp only [Finset.mem_univ,
        IsTotallyComplex.isComplex, iff_self]) f

open Classical in
/--
@isnad1 id=eq.1h2v.s10.aa8386419002 from=translated src=- shape=e4687faa vocab=bc3473ec
-/
theorem prod_infinitePlace_sq_eq_norm_mixedSpaceOfRealSpace
    (q : InfinitePlace K → ℝ) (hq : ∀ w, 0 ≤ q w) :
    (∏ w : InfinitePlace K, q w) ^ 2 =
      mixedEmbedding.norm (mixedSpaceOfRealSpace q) := by
  rw [mixedEmbedding.norm_apply]
  simp only [normAtPlace_mixedSpaceOfRealSpace (hq _),
    IsTotallyComplex.mult_eq, ← Finset.prod_pow]

open Classical in
/--
@isnad1 id=eq.0h2v.s7.4c84771b0db9 from=translated src=- shape=e1b8cfae vocab=68fc07f8
-/
theorem prod_expMapBasis_eq_exp_half_finrank
    (y : realSpace K) :
    ∏ w : InfinitePlace K, expMapBasis y w =
      Real.exp
        (y NumberField.Units.dirichletUnitTheorem.w₀ *
          (Module.finrank ℚ K : ℝ) / 2) := by
  have hleft :
      0 < ∏ w : InfinitePlace K, expMapBasis y w :=
    Finset.prod_pos fun _ _ ↦ expMapBasis_pos _ _
  have hsquare :
      (∏ w : InfinitePlace K, expMapBasis y w) ^ 2 =
        Real.exp
          (y NumberField.Units.dirichletUnitTheorem.w₀ *
            (Module.finrank ℚ K : ℝ)) := by
    rw [prod_infinitePlace_sq_eq_norm_mixedSpaceOfRealSpace K _
      (fun w ↦ (expMapBasis_pos y w).le),
      norm_expMapBasis, ← Real.exp_nat_mul]
    grind
  have hright :
      0 < Real.exp
        (y NumberField.Units.dirichletUnitTheorem.w₀ *
          (Module.finrank ℚ K : ℝ) / 2) :=
    Real.exp_pos _
  apply (sq_eq_sq₀ hleft.le hright.le).mp
  rw [hsquare, pow_two, ← Real.exp_add]
  simp

open Classical in
/--
@isnad1 id=eq.0h2v.s4.0f4aa4a7e894 from=translated src=- shape=d72d682b vocab=af5a6e51
-/
theorem ofReal_exp_cpow (a : ℝ) (s : ℂ) :
    ((Real.exp a : ℝ) : ℂ) ^ s =
      Complex.exp ((a : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero a))]
  rw [← Complex.ofReal_log (Real.exp_pos a).le,
    Real.log_exp]

open Classical in
/--
@isnad1 id=eq.1h2v.s7.44e674a355ff from=translated src=- shape=b70a5fe3 vocab=1d0afaa9
-/
theorem complexPlaceRadialJacobian_eq_prod
    (q : InfinitePlace K → ℝ) (hq : ∀ w, 0 < q w) :
    complexPlaceRadialJacobian K q =
      (∏ w : InfinitePlace K, q w) *
        (2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
          NumberField.Units.regulator K) := by
  rw [complexPlaceRadialJacobian,
    prod_complexPlace_eq_prod_infinitePlace K,
    ← prod_infinitePlace_sq_eq_norm_mixedSpaceOfRealSpace K q
      (fun w ↦ (hq w).le)]
  grind

open Classical in
/--
@isnad1 id=eq.0h4v.s8.02371238e5a7 from=translated src=- shape=d8ac58fd vocab=a0edac02
-/
theorem radialMellinGaussian_eq_prod_cpow_mul_gaussian
    (x : K) (s : ℂ) (y : realSpace K) :
    radialMellinGaussian K x s y =
      (2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
          NumberField.Units.regulator K) •
        (((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
            (2 * s) *
          complexPlaceGaussian K x (expMapBasis y)) := by
  rw [radialMellinGaussian,
    complexPlaceRadialJacobian_eq_prod K _
      (fun w ↦ expMapBasis_pos y w),
    complexPlaceMellinGaussian_eq_prod_cpow_mul_gaussian K x s _
      (fun w ↦ (expMapBasis_pos y w).le)]
  have hp :
      (((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr
      (fun w _ ↦ (expMapBasis_pos y w).ne')
  rw [Complex.real_smul, Complex.real_smul,
    Complex.ofReal_mul]
  calc
    ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) *
          ((2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
              NumberField.Units.regulator K : ℝ) : ℂ) *
          (((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
            (2 * s - 1) *
            complexPlaceGaussian K x (expMapBasis y)) =
        ((2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
              NumberField.Units.regulator K : ℝ) : ℂ) *
          ((((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) *
            ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
              (2 * s - 1)) *
            complexPlaceGaussian K x (expMapBasis y)) := by ring
    _ = _ := by
      congr 2
      calc
        ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) *
              ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
                (2 * s - 1) =
            ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^ 1 *
              ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
                (2 * s - 1) := by simp
        _ = ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
              (1 + (2 * s - 1)) :=
          (Complex.cpow_add _ _ hp).symm
        _ = ((∏ w : InfinitePlace K, expMapBasis y w : ℝ) : ℂ) ^
              (2 * s) := by simp

open Classical in
/--
@isnad1 id=eq.0h4v.s8.69258dee7bc1 from=translated src=- shape=87fc6b80 vocab=25b4e88d
-/
theorem radialMellinGaussian_eq_exp_mul_gaussian
    (x : K) (s : ℂ) (y : realSpace K) :
    radialMellinGaussian K x s y =
      (2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
          NumberField.Units.regulator K) •
        (Complex.exp
            (((y NumberField.Units.dirichletUnitTheorem.w₀ *
                (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s) *
          complexPlaceGaussian K x (expMapBasis y)) := by
  rw [radialMellinGaussian_eq_prod_cpow_mul_gaussian,
    prod_expMapBasis_eq_exp_half_finrank]
  rw [ofReal_exp_cpow]
  push_cast
  ring_nf

open Classical in
/--
@isnad1 id=eq.1h3v.s10.de3504a27cfc from=translated src=- shape=c082db55 vocab=8bc4a423
-/
theorem fundamentalConeZeta_eq_integral_tsum_nonzeroIdealElement_radial
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        fundamentalConeZeta K J s =
      ∫ y in unitFundamentalParamSet K,
        ∑' x : nonzeroIdealElement K J,
          radialMellinGaussian K (((x : 𝓞 K) : K)) s y := by
  have hcone :=
    fundamentalConeZeta_eq_tsum_nonzeroIdealElement_radialIntegral K J hs
  rw [hcone]
  let e := idealElementMulDecompositionEquiv K J
  have hidealSum := summable_idealSet_inverseNormPower K J hs
  have hsupp :
      Function.support
        (fun a : idealSet K J ↦
          (idealSetIntNorm K J a : ℂ) ^ (-s)) = Set.univ := by
    ext a
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    rw [Complex.cpow_ne_zero_iff]
    left
    exact_mod_cast idealSetIntNorm_ne_zero K J a
  have huniv : (Set.univ : Set (idealSet K J)).Countable := by
    rw [← hsupp]
    exact hidealSum.countable_support
  let : Countable (idealSet K J) :=
    Set.countable_univ_iff.mp huniv
  let : Countable (nonzeroIdealElement K J) :=
    Function.Injective.countable e.symm.injective
  apply integral_tsum_of_summable_integral_norm
  · intro x
    exact (integrable_complexPlaceRadialJacobian_smul_mellinGaussian K
      (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
      (lt_trans zero_lt_one hs)).integrableOn
  · rw [← e.summable_iff]
    convert
      summable_prod_integral_norm_radialMellinGaussian_unitSlab K J hs
        using 1
    funext p
    apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
    intro y _
    rw [idealElementMulDecompositionEquiv_coe]

open Classical in
/-- A nonzero ideal shape theta used in the Odlyzko-bound argument. -/
noncomputable def nonzeroIdealShapeTheta
    (J : (Ideal (𝓞 K))⁰) (y : realSpace K) : ℂ :=
  ∑' x : nonzeroIdealElement K J,
    complexPlaceGaussian K (((x : 𝓞 K) : K)) (expMapBasis y)

open Classical in
/--
@isnad1 id=eq.0h4v.s10.7da24bcb47c7 from=translated src=- shape=ff84de66 vocab=a9e25c62
-/
theorem tsum_nonzeroIdealElement_radialMellinGaussian
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) (y : realSpace K) :
    (∑' x : nonzeroIdealElement K J,
      radialMellinGaussian K (((x : 𝓞 K) : K)) s y) =
      (((2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
          NumberField.Units.regulator K : ℝ) : ℂ) *
        Complex.exp
          (((y NumberField.Units.dirichletUnitTheorem.w₀ *
              (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s)) *
        nonzeroIdealShapeTheta K J y := by
  rw [nonzeroIdealShapeTheta, ← tsum_mul_left]
  apply tsum_congr
  intro x
  rw [radialMellinGaussian_eq_exp_mul_gaussian,
    Complex.real_smul]
  ring

open Classical in
/--
@isnad1 id=integrab.1h3v.s9.79d8ae5fb6b2 from=translated src=- shape=4b1618cd vocab=53f12069
-/
theorem integrableOn_logarithmicMellinWeight_mul_nonzeroIdealShapeTheta
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun y ↦
        Complex.exp
            (((y NumberField.Units.dirichletUnitTheorem.w₀ *
                (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s) *
          nonzeroIdealShapeTheta K J y)
      (unitFundamentalParamSet K) := by
  let e := idealElementMulDecompositionEquiv K J
  have hidealSum := summable_idealSet_inverseNormPower K J hs
  have hsupp :
      Function.support
        (fun a : idealSet K J ↦
          (idealSetIntNorm K J a : ℂ) ^ (-s)) = Set.univ := by
    ext a
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    rw [Complex.cpow_ne_zero_iff]
    left
    exact_mod_cast idealSetIntNorm_ne_zero K J a
  have huniv : (Set.univ : Set (idealSet K J)).Countable := by
    rw [← hsupp]
    exact hidealSum.countable_support
  let : Countable (idealSet K J) :=
    Set.countable_univ_iff.mp huniv
  let : Countable (nonzeroIdealElement K J) :=
    Function.Injective.countable e.symm.injective
  have hsum :
      Summable fun x : nonzeroIdealElement K J ↦
        ∫ y in unitFundamentalParamSet K,
          ‖radialMellinGaussian K (((x : 𝓞 K) : K)) s y‖ := by
    rw [← e.summable_iff]
    convert
      summable_prod_integral_norm_radialMellinGaussian_unitSlab K J hs
        using 1
    funext p
    apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
    intro y _
    rw [idealElementMulDecompositionEquiv_coe]
  have htheta :
      IntegrableOn
        (fun y ↦ ∑' x : nonzeroIdealElement K J,
          radialMellinGaussian K (((x : 𝓞 K) : K)) s y)
        (unitFundamentalParamSet K) :=
    integrable_tsum_of_summable_integral_norm
      (fun x ↦
        (integrable_complexPlaceRadialJacobian_smul_mellinGaussian K
          (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
          (lt_trans zero_lt_one hs)).integrableOn)
      hsum
  let c : ℂ :=
    ((2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
      NumberField.Units.regulator K : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    dsimp [c]
    have htwo : 0 < (2⁻¹ : ℝ) ^ nrComplexPlaces K :=
      pow_pos (inv_pos.mpr (by norm_num)) _
    have hfin : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos
    exact (mul_pos (mul_pos htwo hfin)
      (NumberField.Units.regulator_pos K)).ne'
  have hscaled :=
    htheta.const_mul c⁻¹
  apply IntegrableOn.congr_fun hscaled _ measurableSet_unitFundamentalParamSet
  intro y _
  change c⁻¹ * (∑' x : nonzeroIdealElement K J,
      radialMellinGaussian K (((x : 𝓞 K) : K)) s y) =
    Complex.exp
        (((y NumberField.Units.dirichletUnitTheorem.w₀ *
            (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s) *
      nonzeroIdealShapeTheta K J y
  rw [tsum_nonzeroIdealElement_radialMellinGaussian]
  grind

open Classical in
/--
@isnad1 id=eq.1h3v.s9.ef5c4ac31d46 from=translated src=- shape=fddc7a2f vocab=db11524a
-/
theorem fundamentalConeZeta_eq_integral_nonzeroIdealShapeTheta
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        fundamentalConeZeta K J s =
      ∫ y in unitFundamentalParamSet K,
        (((2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
            NumberField.Units.regulator K : ℝ) : ℂ) *
          Complex.exp
            (((y NumberField.Units.dirichletUnitTheorem.w₀ *
                (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s)) *
          nonzeroIdealShapeTheta K J y := by
  rw [fundamentalConeZeta_eq_integral_tsum_nonzeroIdealElement_radial K J hs]
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  exact tsum_nonzeroIdealElement_radialMellinGaussian K J s y

end NumberField.Odlyzko
