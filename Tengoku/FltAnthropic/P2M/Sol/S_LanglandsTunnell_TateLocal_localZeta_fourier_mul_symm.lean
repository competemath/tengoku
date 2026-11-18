import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 4 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell
namespace TateLocal
export _root_.LanglandsTunnell.TateLocal (modulus modulus_coe_units modulus_ne_zero modulus_mul tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta)
open _root_.LanglandsTunnell.TateLocal open _root_.LanglandsTunnell

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

/--
@isnad1 id=eq.1h3v.s7.c0b90310b755 from=translated src=- shape=ce7f8d1d vocab=df34f76e
-/
theorem integral_mulMeasure (μ : Measure K) (F : K → ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
    ∫ x, F x ∂(mulMeasure μ) = ∫ x in ({0}ᶜ : Set K), ((modulus x)⁻¹ : ℝ≥0) • F x ∂μ := by
  have hae : (fun x : K => ((modulus x : ℝ≥0∞))⁻¹)
      =ᵐ[μ.restrict {0}ᶜ] fun x : K => (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine (MeasureTheory.ae_restrict_iff' (MeasurableSet.singleton (0 : K)).compl).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := by simpa using hx
    show ((modulus x : ℝ≥0∞))⁻¹ = (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_inv (modulus_ne_zero hx0)]
  rw [mulMeasure, MeasureTheory.withDensity_congr_ae hae,
    integral_withDensity_eq_integral_smul₀ hm]

/--
@isnad1 id=eq.1h3v.s7.5b3c88c3b314 from=translated src=- shape=87fb9f1f vocab=54966a41
-/
theorem integral_modulus_smul_mulMeasure (μ : Measure K) (F : K → ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
    ∫ x, (modulus x : ℝ) • F x ∂(mulMeasure μ) = ∫ x in ({0}ᶜ : Set K), F x ∂μ := by
  rw [integral_mulMeasure μ _ hm]
  refine MeasureTheory.setIntegral_congr_ae (MeasurableSet.singleton (0 : K)).compl ?_
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx0 : x ≠ 0 := by simpa using hx
  have h1 : ((modulus x)⁻¹ : ℝ≥0) • ((modulus x : ℝ) • F x)
      = (((modulus x)⁻¹ : ℝ≥0) : ℝ) • ((modulus x : ℝ) • F x) := rfl
  rw [h1, smul_smul]
  have : (((modulus x)⁻¹ : ℝ≥0) : ℝ) * (modulus x : ℝ) = 1 := by
    rw [← NNReal.coe_mul, inv_mul_cancel₀ (modulus_ne_zero hx0), NNReal.coe_one]
  rw [this, one_smul]

end LanglandsTunnell.TateLocal

namespace P7Rows
namespace E3b

open _root_.MeasureTheory open _root_.LanglandsTunnell.TateLocal open _root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm.LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

/--
@isnad1 id=eq.0h3v.s7.831e2604d691 from=translated src=- shape=2bce2130 vocab=f55de4b7
-/
theorem preimage_mul_left_eq_smul {K : Type*} [Field K] (u : Kˣ) (s : Set K) :
    (fun x => (u : K) * x) ⁻¹' s = u⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

/--
@isnad1 id=eq.1h3v.s6.093f5e9791ca from=translated src=- shape=05142ca3 vocab=28b108dc
-/
theorem mulMeasure_apply {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] (μ : Measure K) {s : Set K} (hs : MeasurableSet s) :
    mulMeasure μ s = ∫⁻ x in s ∩ {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ ∂μ := by
  rw [mulMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

variable (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

/--
@isnad1 id=eq.0h3v.s7.574058c0da48 from=translated src=- shape=737c2bef vocab=48cab8f0
-/
theorem map_mul_left_eq_smul (u : Kˣ) :
    Measure.map (fun x => (u : K) * x) μ = ((modulus (u : K) : ℝ≥0∞)⁻¹) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, preimage_mul_left_eq_smul,
    Measure.smul_apply, smul_eq_mul, ← distribHaarChar_mul μ u⁻¹ s, map_inv, modulus_coe_units,
    ENNReal.coe_inv distribHaarChar_pos.ne']

/--
@isnad1 id=eq.0h5v.s7.8b0adc4c20d5 from=translated src=- shape=04706da5 vocab=929acac5
-/
theorem setLIntegral_comp_mul_left (u : Kˣ) (F : K → ℝ≥0∞) (T : Set K) :
    ∫⁻ x in (fun x => (u : K) * x) ⁻¹' T, F ((u : K) * x) ∂μ =
      (modulus (u : K) : ℝ≥0∞)⁻¹ * ∫⁻ y in T, F y ∂μ := by
  set e : K ≃ᵐ K := MeasurableEquiv.mulLeft₀ (u : K) u.ne_zero
  have hecoe : (⇑e : K → K) = fun x => (u : K) * x := rfl
  calc ∫⁻ x in (fun x => (u : K) * x) ⁻¹' T, F ((u : K) * x) ∂μ
      = ∫⁻ x, F (e x) ∂(μ.restrict (e ⁻¹' T)) := by rw [hecoe]
    _ = ∫⁻ y, F y ∂((Measure.map e μ).restrict T) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = ∫⁻ y, F y ∂((((modulus (u : K) : ℝ≥0∞)⁻¹) • μ).restrict T) := by
        rw [hecoe, map_mul_left_eq_smul]
    _ = (modulus (u : K) : ℝ≥0∞)⁻¹ * ∫⁻ y in T, F y ∂μ := by
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s7.c104a420f884 from=translated src=- shape=79645ac5 vocab=26851bf1
-/
theorem mulMeasure_map_mul_left [MeasurableSingletonClass K] (u : Kˣ) :
    Measure.map (fun x => (u : K) * x) (mulMeasure μ) = mulMeasure μ := by
  ext s hs
  have hmeas : Measurable fun x => (u : K) * x := measurable_const_mul _
  rw [Measure.map_apply hmeas hs, mulMeasure_apply μ (hmeas hs), mulMeasure_apply μ hs]
  have hpre : (fun x => (u : K) * x) ⁻¹' s ∩ {0}ᶜ = (fun x => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ) := by
    ext x
    simp [Units.ne_zero]
  rw [hpre]
  have hu0 : (modulus (u : K) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero u.ne_zero)
  have hutop : (modulus (u : K) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top

  have hcongr : ∀ x ∈ (fun x => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ),
      ((modulus x : ℝ≥0∞))⁻¹ = (modulus (u : K) : ℝ≥0∞) * ((modulus ((u : K) * x) : ℝ≥0∞))⁻¹ := by
    intro x hx
    have hx0 : x ≠ 0 := by
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        mul_eq_zero, Units.ne_zero, false_or] at hx
      exact hx.2
    rw [modulus_mul, ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop),
      ENNReal.mul_inv_cancel_left hu0 hutop]
  rw [setLIntegral_congr_fun (hmeas (hs.inter (measurableSet_singleton 0).compl)) hcongr,
    lintegral_const_mul' _ _ hutop,
    setLIntegral_comp_mul_left μ u (fun y => ((modulus y : ℝ≥0∞))⁻¹) (s ∩ {0}ᶜ),
    ENNReal.mul_inv_cancel_left hu0 hutop]

/--
@isnad1 id=eq.0h4v.s7.6367179e74fa from=translated src=- shape=cb25ab43 vocab=1c7d41ee
-/
theorem integral_comp_mul_left_mulMeasure [MeasurableSingletonClass K] (u : Kˣ) (F : K → ℂ) :
    ∫ x, F ((u : K) * x) ∂(mulMeasure μ) = ∫ x, F x ∂(mulMeasure μ) := by
  have h := (measurableEmbedding_mulLeft₀ (u.ne_zero : (u : K) ≠ 0)).integral_map
    (μ := mulMeasure μ) F
  rw [mulMeasure_map_mul_left] at h
  exact h.symm

end P7Rows.E3b

namespace P7Rows
namespace E3

open _root_.MeasureTheory open _root_.LanglandsTunnell.TateLocal open _root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm.LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K]

omit [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] in

/--
@isnad1 id=eq.0h4v.s8.bd6945ab81f7 from=translated src=- shape=78cee668 vocab=c6dec4e8
-/
theorem charExt_unit_mul (χ : Kˣ →* ℂˣ) (u : Kˣ) (x : K) :
    charExt χ ((u : K) * x) = ((χ u : ℂˣ) : ℂ) * charExt χ x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hux : (u : K) * x ≠ 0 := mul_ne_zero u.ne_zero hx
    rw [charExt_of_ne_zero _ hux, charExt_of_ne_zero _ hx]
    have h : Units.mk0 ((u : K) * x) hux = u * Units.mk0 x hx := by
      ext
      simp
    rw [h, map_mul, Units.val_mul]

omit [MeasurableSpace K] in

/--
@isnad1 id=eq.0h4v.s6.e687fca6f71f from=translated src=- shape=268ddd45 vocab=24d40fe8
-/
theorem modulus_mul_cpow (a b : K) (w : ℂ) :
    ((modulus (a * b) : ℝ) : ℂ) ^ w
      = ((modulus a : ℝ) : ℂ) ^ w * ((modulus b : ℝ) : ℂ) ^ w := by
  rw [modulus_mul]
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg (modulus a).coe_nonneg (modulus b).coe_nonneg w

/--
@isnad1 id=eventual.0h2v.s6.fb4242226cb2 from=translated src=- shape=6a8d211f vocab=5d4cc7b6
-/
theorem ae_ne_zero_mulMeasure [MeasurableSingletonClass K] (μ : Measure K) :
    ∀ᵐ x ∂(mulMeasure μ), x ≠ 0 := by
  rw [ae_iff]
  have h0 : {x : K | ¬x ≠ 0} = {(0 : K)} := by
    ext x
    simp
  rw [h0, mulMeasure, withDensity_apply _ (MeasurableSet.singleton 0),
    Measure.restrict_restrict (MeasurableSet.singleton 0), Set.inter_compl_self,
    Measure.restrict_empty, lintegral_zero_measure]

/--
@isnad1 id=sfinite.0h2v.s5.b7c047af7e8e from=translated src=- shape=e3ac2196 vocab=b79521c8
-/
theorem sfinite_mulMeasure (μ : Measure K) [SFinite μ] : SFinite (mulMeasure μ) := by
  rw [mulMeasure]
  infer_instance

section Ker

variable (μ : Measure K) [SFinite μ]

def symKer (ψ : AddChar K ℂ) (f g : K → ℂ) (x : K) : ℂ :=
  ∫ p : K × K, f p.1 * g p.2 * ψ (p.1 * p.2 * x) ∂(μ.prod μ)

omit [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] in

/--
@isnad1 id=eq.0h6v.s6.0123f416ab9b from=translated src=- shape=f56998f0 vocab=43ccdb46
-/
theorem symKer_comm (ψ : AddChar K ℂ) (f g : K → ℂ) (x : K) :
    symKer μ ψ f g x = symKer μ ψ g f x := by
  rw [symKer, symKer,
    ← MeasureTheory.integral_prod_swap (fun p : K × K => f p.1 * g p.2 * (ψ (p.1 * p.2 * x) : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show f p.2 * g p.1 * (ψ (p.2 * p.1 * x) : ℂ) = g p.1 * f p.2 * (ψ (p.1 * p.2 * x) : ℂ)
  rw [mul_comm p.2 p.1]
  ring

end Ker

section Main

variable [BorelSpace K] [MeasurableSingletonClass K]
variable (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] [SFinite μ] [NullSingletonClass μ]

private theorem key (ψ : AddChar K ℂ) (f g : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ))
    (hswap : Integrable (Function.uncurry fun y x : K =>
        g y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ f (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hker : ∀ x : K, x ≠ 0 → Integrable
        (fun p : K × K => f p.1 * g p.2 * (ψ (p.1 * p.2 * x) : ℂ)) (μ.prod μ)) :
    localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s
      = ∫ x, (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)) * symKer μ ψ f g x
          ∂(mulMeasure μ) := by
  haveI := sfinite_mulMeasure μ

  have step2 : localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s
      = ∫ y, ∫ x, g y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ f (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
          ∂(mulMeasure μ) ∂(mulMeasure μ) := by
    rw [mul_comm, localZeta, ← integral_mul_const]
    refine integral_congr_ae ((ae_ne_zero_mulMeasure μ).mono fun y hy => ?_)
    dsimp only
    have hinv := P7Rows.E3b.integral_comp_mul_left_mulMeasure (μ := μ) (Units.mk0 y hy)
      (fun x => tateFourier ψ μ f x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
    rw [localZeta, ← hinv, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    have hval : ((Units.mk0 y hy : Kˣ) : K) = y := rfl
    rw [charExt_unit_mul, modulus_mul_cpow, hval]
    have hcy : charExt χ y = ((χ (Units.mk0 y hy) : ℂˣ) : ℂ) := by
      conv_lhs => rw [← hval]
      rw [charExt_coe_units]
    have hinvu : ((χ⁻¹ (Units.mk0 y hy) : ℂˣ) : ℂ)
        = (((χ (Units.mk0 y hy) : ℂˣ) : ℂ))⁻¹ := by
      rw [MonoidHom.inv_apply, ← Units.val_inv_eq_inv_val]
    have hne : ((χ (Units.mk0 y hy) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hmodne : ((modulus y : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by exact_mod_cast modulus_ne_zero hy)
    have hmodpow : ((modulus y : ℝ) : ℂ) ^ s * ((modulus y : ℝ) : ℂ) ^ (1 - s)
        = ((modulus y : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hmodne]
      norm_num
    have hainv : ((χ (Units.mk0 y hy) : ℂˣ) : ℂ) * (((χ (Units.mk0 y hy) : ℂˣ) : ℂ))⁻¹ = 1 :=
      mul_inv_cancel₀ hne
    rw [hcy, hinvu]
    linear_combination (g y * tateFourier ψ μ f (y * x) * charExt χ⁻¹ x *
        ((modulus x : ℝ) : ℂ) ^ (1 - s) * ((modulus y : ℝ) : ℂ) ^ s *
        ((modulus y : ℝ) : ℂ) ^ (1 - s)) * hainv +
      (g y * tateFourier ψ μ f (y * x) * charExt χ⁻¹ x *
        ((modulus x : ℝ) : ℂ) ^ (1 - s)) * hmodpow
  rw [step2, integral_integral_swap hswap]

  refine integral_congr_ae ((ae_ne_zero_mulMeasure μ).mono fun x hx => ?_)
  dsimp only
  have hinner1 : (fun y : K => g y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ f (y * x) *
        (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      = fun y : K => ((modulus y : ℝ) • (g y * tateFourier ψ μ f (y * x))) *
        (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)) := by
    funext y
    rw [Complex.real_smul]
    ring
  rw [hinner1, integral_mul_const, integral_modulus_smul_mulMeasure μ _ hm]

  have hfull : μ.restrict ({0}ᶜ : Set K) = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    have h0 : {y : K | y ∉ ({0}ᶜ : Set K)} = {(0 : K)} := by
      ext y
      simp
    rw [h0]
    exact measure_singleton 0
  have hset : (∫ y in ({0}ᶜ : Set K), g y * tateFourier ψ μ f (y * x) ∂μ)
      = ∫ y, g y * tateFourier ψ μ f (y * x) ∂μ := by
    rw [show (∫ y in ({0}ᶜ : Set K), g y * tateFourier ψ μ f (y * x) ∂μ)
        = ∫ y, g y * tateFourier ψ μ f (y * x) ∂(μ.restrict ({0}ᶜ : Set K)) from rfl, hfull]
  rw [hset]

  have hker' : Integrable (Function.uncurry fun y z : K =>
      g y * (f z * (ψ (z * y * x) : ℂ))) (μ.prod μ) := by
    refine ((hker x hx).swap).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, Function.uncurry, Prod.fst_swap, Prod.snd_swap]
    ring
  have hunfold : (fun y : K => g y * tateFourier ψ μ f (y * x))
      = fun y : K => ∫ z, g y * (f z * (ψ (z * y * x) : ℂ)) ∂μ := by
    funext y
    rw [tateFourier, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [mul_assoc z y x]
  rw [hunfold, integral_integral_swap hker', mul_comm]
  congr 1
  rw [symKer, MeasureTheory.integral_prod _ (hker x hx)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  ring

/--
@isnad1 id=eq.4h7v.s10.64856e1840ca from=translated src=- shape=4196b35f vocab=b789acd2
-/
theorem localZeta_fourier_mul_symm (ψ : AddChar K ℂ) (f g : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ))
    (hswapL : Integrable (Function.uncurry fun y x : K =>
        g y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ f (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hswapR : Integrable (Function.uncurry fun y x : K =>
        f y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ g (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hker : ∀ x : K, x ≠ 0 → Integrable
        (fun p : K × K => f p.1 * g p.2 * (ψ (p.1 * p.2 * x) : ℂ)) (μ.prod μ)) :
    localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s
      = localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s := by
  have hkerR : ∀ x : K, x ≠ 0 → Integrable
      (fun p : K × K => g p.1 * f p.2 * (ψ (p.1 * p.2 * x) : ℂ)) (μ.prod μ) := by
    intro x hx
    refine ((hker x hx).swap).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
    rw [mul_comm p.2 p.1]
    ring
  rw [key μ ψ f g χ s hm hswapL hker, key μ ψ g f χ s hm hswapR hkerR]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [symKer_comm]

end Main

end P7Rows.E3

end

set_option autoImplicit false
open _root_.MeasureTheory open _root_.LanglandsTunnell.TateLocal open _root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm.LanglandsTunnell.TateLocal
open scoped NNReal

/--
@isnad1 id=eq.4h7v.s10.64856e1840ca from=translated src=- shape=4196b35f vocab=b789acd2
-/
theorem solution {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableSingletonClass K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] [SFinite μ]
    [NullSingletonClass μ] (ψ : AddChar K ℂ) (f g : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ))
    (hswapL : Integrable (Function.uncurry fun y x : K =>
        g y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ f (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hswapR : Integrable (Function.uncurry fun y x : K =>
        f y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ g (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hker : ∀ x : K, x ≠ 0 → Integrable
        (fun p : K × K => f p.1 * g p.2 * (ψ (p.1 * p.2 * x) : ℂ)) (μ.prod μ)) :
    localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s
      = localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s := by
  apply P7Rows.E3.localZeta_fourier_mul_symm <;> assumption
