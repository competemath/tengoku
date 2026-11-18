import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow

set_option autoImplicit false

open MeasureTheory

namespace ShellDecomp

variable {Ω : Type*} [MeasurableSpace Ω]

/--
@isnad1 id=measurab.1h3v.s5.3dca010b49ac from=translated src=- shape=9d653c36 vocab=bc917733
-/
theorem measurable_const_zpow (c : ℂ) {E : Ω → ℤ} (hE : Measurable E) :
    Measurable fun ω => c ^ E ω :=
  (measurable_of_countable fun n : ℤ => c ^ n).comp hE

/--
@isnad1 id=measurab.1h3v.s5.723bf1ea3c37 from=translated src=- shape=34176597 vocab=3692caaf
-/
theorem measurableSet_fiber {E : Ω → ℤ} (hE : Measurable E) (n : ℤ) :
    MeasurableSet (E ⁻¹' {n}) :=
  hE (measurableSet_singleton n)

omit [MeasurableSpace Ω] in
/--
@isnad1 id=eq.0h2v.s4.e1b23913a9e8 from=translated src=- shape=215d25ea vocab=363c5db0
-/
theorem iUnion_fiber (E : Ω → ℤ) : (⋃ n : ℤ, E ⁻¹' {n}) = Set.univ := by
  ext ω; simp

omit [MeasurableSpace Ω] in

/--
@isnad1 id=eq.1h6v.s6.2ec0d2db4bcf from=translated src=- shape=15f1e81c vocab=89b51aeb
-/
theorem norm_mul_zpow (G : Ω → ℂ) (E : Ω → ℤ) {Y : ℂ} {r : ℝ} (hY : ‖Y‖ = r) (ω : Ω) :
    ‖G ω * Y ^ E ω‖ = ‖G ω‖ * r ^ E ω := by
  rw [norm_mul, norm_zpow, hY]

/--
@isnad1 id=aestrong.3h5v.s6.c758ebe2f99c from=translated src=- shape=710d5afc vocab=e1fa361b
-/
theorem aestronglyMeasurable_of_mul_zpow (ρ : Measure Ω) {E : Ω → ℤ} (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : AEStronglyMeasurable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    AEStronglyMeasurable G ρ := by
  have hne : ∀ ω, ((r : ℂ) ^ E ω) ≠ 0 := fun ω =>
    zpow_ne_zero _ (by exact_mod_cast hr.ne')
  have h2 : AEStronglyMeasurable (fun ω => ((r : ℂ) ^ E ω)⁻¹) ρ :=
    (measurable_const_zpow (r : ℂ) hE).inv.aestronglyMeasurable
  have := hG.mul h2
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  show G ω * (r : ℂ) ^ E ω * ((r : ℂ) ^ E ω)⁻¹ = G ω
  rw [mul_assoc, mul_inv_cancel₀ (hne ω), mul_one]

/--
@isnad1 id=integrab.4h6v.s7.d03fea85c7f8 from=translated src=- shape=43ed6dca vocab=59031f17
-/
theorem integrable_mul_zpow_of_norm_eq (ρ : Measure Ω) {E : Ω → ℤ} (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) {Y : ℂ} (hY : ‖Y‖ = r) :
    Integrable (fun ω => G ω * Y ^ E ω) ρ := by
  have hGm : AEStronglyMeasurable G ρ := aestronglyMeasurable_of_mul_zpow ρ hE G hr hG.1
  have hm : AEStronglyMeasurable (fun ω => G ω * Y ^ E ω) ρ :=
    hGm.mul (measurable_const_zpow Y hE).aestronglyMeasurable
  refine hG.congr' hm (Filter.Eventually.of_forall fun ω => ?_)
  have hr' : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [norm_mul_zpow G E hr', norm_mul_zpow G E hY]

/--
@isnad1 id=integrab.2h5v.s7.83c784a74410 from=translated src=- shape=e7cd5dd8 vocab=93684fb1
-/
theorem integrable_norm_mul_zpow (ρ : Measure Ω) {E : Ω → ℤ}
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    Integrable (fun ω => ‖G ω‖ * r ^ E ω) ρ := by
  have hr' : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have := hG.norm
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact norm_mul_zpow G E hr' ω

end ShellDecomp

open ShellDecomp in

/--
@isnad1 id=and.3h5v.s8.5df4686409d5 from=translated src=- shape=336929ca vocab=617fa596
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (E : Ω → ℤ) (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n) (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) ∧
    (Summable fun n : ℤ => ‖∫ ω in E ⁻¹' {n}, G ω ∂ρ‖ * r ^ n) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      Integrable (fun ω => G ω * Y ^ E ω) ρ ∧
      HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, G ω ∂ρ) * Y ^ n) (∫ ω, G ω * Y ^ E ω ∂ρ) := by
  have hms : ∀ n : ℤ, MeasurableSet (E ⁻¹' {n}) := measurableSet_fiber hE
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℤ => E ⁻¹' {n}) := pairwise_disjoint_fiber E

  have hreal : HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n)
      (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) := by
    have hint : Integrable (fun ω => ‖G ω‖ * r ^ E ω) ρ := integrable_norm_mul_zpow ρ G hr hG
    have h := hasSum_integral_iUnion (μ := ρ) (f := fun ω => ‖G ω‖ * r ^ E ω) hms hdisj
      (by rw [iUnion_fiber]; exact hint.integrableOn)
    rw [iUnion_fiber, Measure.restrict_univ] at h
    refine h.congr_fun fun n => ?_

    have : ∫ ω in E ⁻¹' {n}, ‖G ω‖ * r ^ E ω ∂ρ = ∫ ω in E ⁻¹' {n}, ‖G ω‖ * r ^ n ∂ρ := by
      refine setIntegral_congr_fun (hms n) fun ω hω => ?_
      have hn : E ω = n := by simpa using hω
      simp only [hn]
    rw [this, integral_mul_const]
  refine ⟨hreal, ?_, ?_⟩
  ·
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n))
      (fun n => ?_) hreal.summable
    exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (zpow_nonneg hr.le n)
  ·
    intro Y hY
    have hint : Integrable (fun ω => G ω * Y ^ E ω) ρ := integrable_mul_zpow_of_norm_eq ρ hE G hr hG hY
    refine ⟨hint, ?_⟩
    have h := hasSum_integral_iUnion (μ := ρ) (f := fun ω => G ω * Y ^ E ω) hms hdisj
      (by rw [iUnion_fiber]; exact hint.integrableOn)
    rw [iUnion_fiber, Measure.restrict_univ] at h
    refine h.congr_fun fun n => ?_
    have : ∫ ω in E ⁻¹' {n}, G ω * Y ^ E ω ∂ρ = ∫ ω in E ⁻¹' {n}, G ω * Y ^ n ∂ρ := by
      refine setIntegral_congr_fun (hms n) fun ω hω => ?_
      have hn : E ω = n := by simpa using hω
      simp only [hn]
    rw [this, integral_mul_const]
