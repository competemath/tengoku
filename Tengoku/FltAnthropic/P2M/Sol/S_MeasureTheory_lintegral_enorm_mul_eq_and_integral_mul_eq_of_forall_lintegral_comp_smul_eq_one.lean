import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal NNReal

noncomputable section

namespace KcSectionIndep

variable {A X : Type*} [Group A] [MulAction A X] [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
variable (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
variable (ρ : Measure X) [SFinite ρ]

/--
@isnad1 id=eq.8h7v.s8.040859c82e6d from=translated src=- shape=5c8e3efc vocab=922c4cbc
-/
theorem lintegral_indep (hact : Measurable fun z : A × X => z.1 • z.2)
    (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    {k : X → ℝ≥0∞} (hk : Measurable k) (hkinv : ∀ (a : A) (x : X), k (a • x) = k x)
    {w₁ w₂ : X → ℝ} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hs₁ : ∀ x, k x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, k x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, k x * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, k x * ENNReal.ofReal (w₂ x) ∂ρ := by
  set W₁ : X → ℝ≥0∞ := fun x => ENNReal.ofReal (w₁ x) with hW₁
  set W₂ : X → ℝ≥0∞ := fun x => ENNReal.ofReal (w₂ x) with hW₂
  have hW₁m : Measurable W₁ := ENNReal.measurable_ofReal.comp hw₁
  have hW₂m : Measurable W₂ := ENNReal.measurable_ofReal.comp hw₂
  have hactx : ∀ x : X, Measurable fun a : A => a • x := fun x =>
    hact.comp (measurable_id.prodMk measurable_const)
  have hacta : ∀ a : A, Measurable fun x : X => a • x := fun a =>
    hact.comp (measurable_const.prodMk measurable_id)

  have h1 : ∫⁻ x, k x * W₁ x ∂ρ = ∫⁻ x, ∫⁻ a, k x * W₁ x * W₂ (a • x) ∂τ ∂ρ := by
    refine lintegral_congr fun x => ?_
    have hm : Measurable fun a : A => W₂ (a • x) := hW₂m.comp (hactx x)
    rw [lintegral_const_mul _ hm]
    by_cases hkx : k x = 0
    · simp [hkx]
    · rw [hs₂ x hkx, mul_one]

  have hF : Measurable fun z : X × A => k z.1 * W₁ z.1 * W₂ (z.2 • z.1) :=
    ((hk.comp measurable_fst).mul (hW₁m.comp measurable_fst)).mul
      (hW₂m.comp (hact.comp (measurable_snd.prodMk measurable_fst)))
  have h2 : ∫⁻ x, ∫⁻ a, k x * W₁ x * W₂ (a • x) ∂τ ∂ρ = ∫⁻ a, ∫⁻ x, k x * W₁ x * W₂ (a • x) ∂ρ ∂τ :=
    lintegral_lintegral_swap hF.aemeasurable
  have h3 : ∀ a : A, ∫⁻ x, k x * W₁ x * W₂ (a • x) ∂ρ = ∫⁻ x, k x * W₁ (a⁻¹ • x) * W₂ x ∂ρ := by
    intro a
    have hH : Measurable fun x : X => k x * W₁ (a⁻¹ • x) * W₂ x :=
      (hk.mul (hW₁m.comp (hacta a⁻¹))).mul hW₂m
    rw [← (hρ a).lintegral_comp hH]
    refine lintegral_congr fun x => ?_
    simp only [hkinv, inv_smul_smul]
  have hF' : Measurable fun z : A × X => k z.2 * W₁ (z.1⁻¹ • z.2) * W₂ z.2 := by
    have hm : Measurable fun z : A × X => z.1⁻¹ • z.2 :=
      hact.comp ((measurable_fst.inv).prodMk measurable_snd)
    exact ((hk.comp measurable_snd).mul (hW₁m.comp hm)).mul (hW₂m.comp measurable_snd)
  have h4 : ∫⁻ a, ∫⁻ x, k x * W₁ (a⁻¹ • x) * W₂ x ∂ρ ∂τ = ∫⁻ x, ∫⁻ a, k x * W₁ (a⁻¹ • x) * W₂ x ∂τ ∂ρ :=
    lintegral_lintegral_swap hF'.aemeasurable

  have h5 : ∀ x : X, ∫⁻ a, k x * W₁ (a⁻¹ • x) * W₂ x ∂τ = k x * W₂ x * ∫⁻ a, W₁ (a • x) ∂τ := by
    intro x
    have hm : Measurable fun a : A => W₁ (a⁻¹ • x) := hW₁m.comp ((hactx x).comp measurable_inv)
    simp_rw [mul_right_comm (k x)]
    rw [lintegral_const_mul _ hm]
    congr 1
    exact lintegral_inv_eq_self (μ := τ) (fun a : A => W₁ (a • x))
  rw [h1, h2]
  simp_rw [h3]
  rw [h4]
  simp_rw [h5]
  refine lintegral_congr fun x => ?_
  by_cases hkx : k x = 0
  · simp [hkx]
  · rw [hs₁ x hkx, mul_one]

variable {h : X → ℂ} {w₁ w₂ : X → ℝ}

/--
@isnad1 id=eq.12h8v.s8.12c61c48f690 from=translated src=- shape=89d3d7fa vocab=8fa2c1fc
-/
theorem lintegral_ofReal_indep (hact : Measurable fun z : A × X => z.1 • z.2)
    (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    (hh : Measurable h) (hhinv : ∀ (a : A) (x : X), h (a • x) = h x)
    (c : ℂ → ℝ) (hc : Measurable c) (hc0 : c 0 = 0)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hs₁ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ENNReal.ofReal (c (h x) * w₁ x) ∂ρ = ∫⁻ x, ENNReal.ofReal (c (h x) * w₂ x) ∂ρ := by
  have hk : Measurable fun x : X => ENNReal.ofReal (c (h x)) := ENNReal.measurable_ofReal.comp (hc.comp hh)
  have hne : ∀ x : X, ENNReal.ofReal (c (h x)) ≠ 0 → h x ≠ 0 := by
    intro x hx h0
    apply hx
    rw [h0, hc0, ENNReal.ofReal_zero]
  have := lintegral_indep τ ρ hact hρ hk (fun a x => by simp only [hhinv]) hw₁ hw₂
    (fun x hx => hs₁ x (hne x hx)) (fun x hx => hs₂ x (hne x hx))
  simp only [← ENNReal.ofReal_mul' (hw₁0 _), ← ENNReal.ofReal_mul' (hw₂0 _)] at this
  exact this

/--
@isnad1 id=eq.1h2v.s6.dca8f298351f from=translated src=- shape=bfb931a6 vocab=dc66d824
-/
theorem enorm_real_mul {z : ℂ} {r : ℝ} (hr : 0 ≤ r) : ‖z * (r : ℂ)‖ₑ = ‖z‖ₑ * ENNReal.ofReal r := by
  rw [enorm_mul]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

/--
@isnad1 id=and.10h7v.s9.03fa83cf16b9 from=translated src=- shape=9300c0d2 vocab=7b0239e8
-/
theorem main (hact : Measurable fun z : A × X => z.1 • z.2)
    (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    (hh : Measurable h) (hhinv : ∀ (a : A) (x : X), h (a • x) = h x)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hs₁ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₂ x) ∂ρ ∧
      (Integrable (fun x => h x * (w₁ x : ℂ)) ρ →
        Integrable (fun x => h x * (w₂ x : ℂ)) ρ ∧
          ∫ x, h x * (w₁ x : ℂ) ∂ρ = ∫ x, h x * (w₂ x : ℂ) ∂ρ) := by

  have hne : ∀ x : X, ‖h x‖ₑ ≠ 0 → h x ≠ 0 := fun x hx h0 => hx (by rw [h0, enorm_zero])
  have hL : ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₂ x) ∂ρ :=
    lintegral_indep τ ρ hact hρ hh.enorm (fun a x => by simp only [hhinv]) hw₁ hw₂
      (fun x hx => hs₁ x (hne x hx)) (fun x hx => hs₂ x (hne x hx))
  refine ⟨hL, fun hint => ?_⟩
  have hm₂ : Measurable fun x => h x * (w₂ x : ℂ) := hh.mul (Complex.measurable_ofReal.comp hw₂)
  have hint₂ : Integrable (fun x => h x * (w₂ x : ℂ)) ρ := by
    refine ⟨hm₂.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [enorm_real_mul (hw₂0 _)]
    rw [← hL]
    simp_rw [← enorm_real_mul (hw₁0 _)]
    exact hint.2
  refine ⟨hint₂, ?_⟩

  have key : ∀ (c : ℂ → ℝ), Measurable c → c 0 = 0 →
      ∫⁻ x, ENNReal.ofReal (c (h x) * w₁ x) ∂ρ = ∫⁻ x, ENNReal.ofReal (c (h x) * w₂ x) ∂ρ :=
    fun c hc hc0 => lintegral_ofReal_indep τ ρ hact hρ hh hhinv c hc hc0 hw₁ hw₂ hw₁0 hw₂0 hs₁ hs₂
  have hre : ∀ (w : X → ℝ) (x : X), RCLike.re (h x * (w x : ℂ)) = Complex.re (h x) * w x := by
    intro w x; simp
  have him : ∀ (w : X → ℝ) (x : X), RCLike.im (h x * (w x : ℂ)) = Complex.im (h x) * w x := by
    intro w x; simp
  have hreI : ∀ {w : X → ℝ}, Integrable (fun x => h x * (w x : ℂ)) ρ →
      ∫ x, RCLike.re (h x * (w x : ℂ)) ∂ρ =
        (∫⁻ x, ENNReal.ofReal (Complex.re (h x) * w x) ∂ρ).toReal -
          (∫⁻ x, ENNReal.ofReal ((-Complex.re (h x)) * w x) ∂ρ).toReal := by
    intro w hw
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hw.re]
    simp only [hre, neg_mul]
  have himI : ∀ {w : X → ℝ}, Integrable (fun x => h x * (w x : ℂ)) ρ →
      ∫ x, RCLike.im (h x * (w x : ℂ)) ∂ρ =
        (∫⁻ x, ENNReal.ofReal (Complex.im (h x) * w x) ∂ρ).toReal -
          (∫⁻ x, ENNReal.ofReal ((-Complex.im (h x)) * w x) ∂ρ).toReal := by
    intro w hw
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hw.im]
    simp only [him, neg_mul]
  rw [← integral_re_add_im hint, ← integral_re_add_im hint₂, hreI hint, hreI hint₂, himI hint, himI hint₂,
    key Complex.re Complex.measurable_re Complex.zero_re,
    key (fun z => -Complex.re z) Complex.measurable_re.neg (by simp),
    key Complex.im Complex.measurable_im Complex.zero_im,
    key (fun z => -Complex.im z) Complex.measurable_im.neg (by simp)]

end KcSectionIndep

end

open KcSectionIndep in
/--
@isnad1 id=and.10h7v.s9.752d1b0f7814 from=translated src=- shape=afa1c0c6 vocab=7b0239e8
-/
theorem solution
    {A X : Type*} [Group A] [MulAction A X] [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
    (hact : Measurable fun z : A × X => z.1 • z.2)
    (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
    (ρ : Measure X) [SFinite ρ] (hρ : ∀ a : A, MeasurePreserving (fun x : X => a • x) ρ ρ)
    (h : X → ℂ) (hh : Measurable h) (hhA : ∀ (a : A) (x : X), h (a • x) = h x)
    (w₁ w₂ : X → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hs₁ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (hs₂ : ∀ x, h x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₁ x) ∂ρ = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (w₂ x) ∂ρ ∧
      (Integrable (fun x => h x * (w₁ x : ℂ)) ρ →
        Integrable (fun x => h x * (w₂ x : ℂ)) ρ ∧
          ∫ x, h x * (w₁ x : ℂ) ∂ρ = ∫ x, h x * (w₂ x : ℂ) ∂ρ) :=
  main τ ρ hact hρ hh hhA hw₁ hw₂ hw₁0 hw₂0 hs₁ hs₂
