import Tengoku.FltAnthropic.Theorems.Thm_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
import Tengoku.FltAnthropic.Theorems.Thm_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top

set_option autoImplicit false

noncomputable section

open SchwartzMap MeasureTheory FourierTransform LineDeriv Real Complex
open scoped InnerProductSpace

namespace R4P1Engine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def linC (a : V) : V → ℂ := fun y => ((⟪y, a⟫_ℝ : ℝ) : ℂ)

/--
@isnad1 id=eq.0h3v.s6.a423217c71f4 from=translated src=- shape=67e61c59 vocab=160b2168
-/
theorem linC_apply (a : V) (y : V) : linC a y = ((⟪y, a⟫_ℝ : ℝ) : ℂ) := rfl

/--
@isnad1 id=hastempe.0h2v.s6.46fe146a5760 from=translated src=- shape=d019e5bf vocab=b369c98b
-/
theorem hasTemperateGrowth_inner (a : V) : (fun y : V => ⟪y, a⟫_ℝ).HasTemperateGrowth := by
  fun_prop

/--
@isnad1 id=hastempe.0h2v.s6.8dbdc3053493 from=translated src=- shape=b5c49b2c vocab=6090d0b4
-/
theorem hasTemperateGrowth_linC (a : V) : (linC a).HasTemperateGrowth := by
  unfold linC; fun_prop

def Mr (a : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := smulLeftCLM ℂ (linC a)

/--
@isnad1 id=eq.0h4v.s9.31c1c7991668 from=translated src=- shape=099ee29f vocab=82acd1d8
-/
theorem Mr_apply_apply (a : V) (f : 𝓢(V, ℂ)) (y : V) : Mr a f y = ((⟪y, a⟫_ℝ : ℝ) : ℂ) * f y := by
  rw [Mr, smulLeftCLM_apply_apply (hasTemperateGrowth_linC a), smul_eq_mul, linC_apply]

/--
@isnad1 id=eq.0h3v.s10.4cd4c2dce8c9 from=translated src=- shape=a74869ca vocab=5c51df62
-/
theorem Mr_eq_smulLeftCLM_real (a : V) (f : 𝓢(V, ℂ)) :
    Mr a f = smulLeftCLM ℂ (fun y : V => ⟪y, a⟫_ℝ) f := by
  rw [Mr]
  have := smulLeftCLM_ofReal (𝕜' := ℂ) (F := ℂ) (hasTemperateGrowth_inner a) f
  exact this

def Dd (v : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := lineDerivOpCLM ℂ 𝓢(V, ℂ) v

/--
@isnad1 id=eq.0h3v.s9.4a71e73e83ea from=translated src=- shape=ed2bf5ba vocab=e18c7647
-/
theorem Dd_apply (v : V) (f : 𝓢(V, ℂ)) : Dd v f = ∂_{v} f := rfl

/--
@isnad1 id=eq.0h4v.s10.f8f2b6f656cf from=translated src=- shape=a7a11b0a vocab=46fb0bdd
-/
theorem Dd_apply_apply (v : V) (f : 𝓢(V, ℂ)) (y : V) : Dd v f y = fderiv ℝ (⇑f) y v := rfl

/--
@isnad1 id=eq.0h3v.s10.2c141e020bd8 from=translated src=- shape=756a9c49 vocab=190aa892
-/
theorem fourier_Dd (v : V) (f : 𝓢(V, ℂ)) :
    𝓕 (Dd v f) = (2 * π * Complex.I) • Mr v (𝓕 f) := by
  rw [Dd_apply, fourier_lineDerivOp_eq, Mr_eq_smulLeftCLM_real]

/--
@isnad1 id=eq.0h3v.s10.44a8436e3c8a from=translated src=- shape=370c3825 vocab=a2ac0dbc
-/
theorem fourier_Mr (a : V) (f : 𝓢(V, ℂ)) :
    𝓕 (Mr a f) = (-(2 * π * Complex.I))⁻¹ • Dd a (𝓕 f) := by
  have h := lineDerivOp_fourier_eq f a

  rw [FourierSMul.fourier_smul, ← Mr_eq_smulLeftCLM_real] at h
  have hc : (-(2 * (π : ℂ) * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [Dd_apply, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
variable (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V)

def avec (i : ι) (k : κ) : V := ContinuousLinearMap.adjoint (B i) (b k)

def cst (i : ι) (k : κ) : ℂ := ((⟪v i, b k⟫_ℝ : ℝ) : ℂ)

/--
@isnad1 id=eq.0h8v.s8.bdde89f7d7e4 from=translated src=- shape=61570516 vocab=c49dca88
-/
theorem inner_avec (i : ι) (k : κ) (y : V) : ⟪y, avec B b i k⟫_ℝ = ⟪B i y, b k⟫_ℝ := by
  rw [avec, ContinuousLinearMap.adjoint_inner_right]

def Malpha (i : ι) (k : κ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  cst v b i k • ContinuousLinearMap.id ℂ _ + Mr (avec B b i k)

/--
@isnad1 id=eq.0h10v.s10.c902821ea1cb from=translated src=- shape=f6b36360 vocab=defc87fe
-/
theorem Malpha_apply_apply (i : ι) (k : κ) (f : 𝓢(V, ℂ)) (y : V) :
    Malpha B v b i k f y = ((⟪B i y + v i, b k⟫_ℝ : ℝ) : ℂ) * f y := by
  simp only [Malpha, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, add_apply, smul_apply, smul_eq_mul,
    Mr_apply_apply, inner_avec, cst, inner_add_left]
  push_cast
  ring

def Chat (i : ι) (k : κ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  cst v b i k • ContinuousLinearMap.id ℂ _ + (-(2 * π * Complex.I))⁻¹ • Dd (avec B b i k)

/--
@isnad1 id=eq.0h9v.s10.2b4b051e66b8 from=translated src=- shape=4ad8e72d vocab=c16a22c6
-/
theorem fourier_Malpha (i : ι) (k : κ) (f : 𝓢(V, ℂ)) :
    𝓕 (Malpha B v b i k f) = Chat B v b i k (𝓕 f) := by
  simp only [Malpha, Chat, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, FourierAdd.fourier_add, FourierSMul.fourier_smul, fourier_Mr]

def LapS : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  ∑ i, ∑ k, ∑ l, (Malpha B v b i k).comp ((Malpha B v b i l).comp ((Dd (b k)).comp (Dd (b l))))

def LapHat : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  ∑ i, ∑ k, ∑ l, ((2 * π * Complex.I) ^ 2 : ℂ) •
    (Chat B v b i k).comp ((Chat B v b i l).comp ((Mr (b k)).comp (Mr (b l))))

/--
@isnad1 id=eq.0h7v.s10.2a0c664acaec from=translated src=- shape=989fad70 vocab=5d0c72fd
-/
theorem fourier_LapS (f : 𝓢(V, ℂ)) : 𝓕 (LapS B v b f) = LapHat B v b (𝓕 f) := by
  simp only [LapS, LapHat, sum_apply, ContinuousLinearMap.comp_apply,
    smul_apply]
  rw [FourierTransform.fourier_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FourierTransform.fourier_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [FourierTransform.fourier_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fourier_Malpha, fourier_Malpha, fourier_Dd, map_smul, fourier_Dd, map_smul, map_smul, map_smul,
    map_smul, smul_smul, pow_two]

/--
@isnad1 id=eq.0h8v.s10.c1852ecd435f from=translated src=- shape=65f4087f vocab=eddf61fa
-/
theorem fourier_LapS_iterate (m : ℕ) (f : 𝓢(V, ℂ)) :
    𝓕 ((LapS B v b)^[m] f) = (LapHat B v b)^[m] (𝓕 f) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fourier_LapS, ih]

/--
@isnad1 id=eq.1h5v.s11.1901d809a90e from=translated src=- shape=e99d06f0 vocab=569b6d8f
-/
theorem fderiv_fderiv_apply {G : V → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (y u w : V) :
    fderiv ℝ (fderiv ℝ G) y u w = fderiv ℝ (fun z => fderiv ℝ G z w) y u := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y := (h1.differentiable (by simp)).differentiableAt
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w y)).fderiv
  rw [this]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply, zero_add]

/--
@isnad1 id=eq.0h5v.s11.b6a8c3d748e7 from=translated src=- shape=a0489dff vocab=41446a9c
-/
theorem Dd_Dd_apply (u w : V) (f : 𝓢(V, ℂ)) (y : V) :
    Dd u (Dd w f) y = fderiv ℝ (fderiv ℝ (⇑f)) y u w := by
  rw [Dd_apply_apply]
  have : (⇑(Dd w f) : V → ℂ) = fun z => fderiv ℝ (⇑f) z w := by
    funext z; rfl
  rw [this, fderiv_fderiv_apply (f.smooth ⊤)]

/--
@isnad1 id=eq.0h6v.s12.230c083d7c9b from=translated src=- shape=94257e12 vocab=e545cf4f
-/
theorem fderiv_fderiv_expand (f : 𝓢(V, ℂ)) (y x : V) :
    fderiv ℝ (fderiv ℝ (⇑f)) y x x =
      ∑ k, ∑ l, ((⟪x, b k⟫_ℝ : ℝ) : ℂ) * ((⟪x, b l⟫_ℝ : ℝ) : ℂ) * fderiv ℝ (fderiv ℝ (⇑f)) y (b k) (b l) := by
  set L := fderiv ℝ (fderiv ℝ (⇑f)) y with hL
  have hx : x = ∑ k, ⟪x, b k⟫_ℝ • b k := by
    conv_lhs => rw [← b.sum_repr' x]
    simp_rw [real_inner_comm]
  have step1 : L x = ∑ k, ⟪x, b k⟫_ℝ • L (b k) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul]
  have step2 : ∀ k, L (b k) x = ∑ l, ⟪x, b l⟫_ℝ • L (b k) (b l) := by
    intro k
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul]
  rw [step1, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, step2 k, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.real_smul, Complex.real_smul]
  ring

/--
@isnad1 id=eq.0h8v.s10.5ce5d01739dc from=translated src=- shape=fb17cbe4 vocab=4523969c
-/
theorem LapS_apply (f : 𝓢(V, ℂ)) (y : V) :
    LapS B v b f y = ∑ i, iteratedFDeriv ℝ 2 (⇑f) y (fun _ => B i y + v i) := by
  simp only [LapS, sum_apply, ContinuousLinearMap.comp_apply, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_expand b f y (B i y + v i)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Malpha_apply_apply, Malpha_apply_apply, Dd_Dd_apply]
  ring

section Duality

/--
@isnad1 id=hastempe.1h2v.s8.e6283d9e1b0f from=translated src=- shape=3de6fec1 vocab=5b8456fc
-/
theorem hasTemperateGrowth_fderiv' {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    (fderiv ℝ r).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hr.1).2, fun n => ?_⟩
  obtain ⟨k, C, hC⟩ := hr.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hC x⟩

/--
@isnad1 id=hastempe.1h3v.s8.480589d035fa from=translated src=- shape=19a4cab0 vocab=9ceb2203
-/
theorem hasTemperateGrowth_fderiv_apply {r : V → ℂ} (hr : r.HasTemperateGrowth) (a : V) :
    (fun ξ => fderiv ℝ r ξ a).HasTemperateGrowth := by
  have h := (ContinuousLinearMap.apply ℝ ℂ a).hasTemperateGrowth.comp (hasTemperateGrowth_fderiv' hr)
  exact h

/--
@isnad1 id=hastempe.1h3v.s6.a3517d2a9d29 from=translated src=- shape=bac91521 vocab=7dbc34f9
-/
theorem hasTemperateGrowth_linC_mul {r : V → ℂ} (hr : r.HasTemperateGrowth) (a : V) :
    (fun ξ => linC a ξ * r ξ).HasTemperateGrowth :=
  (hasTemperateGrowth_linC a).mul hr

/--
@isnad1 id=integrab.1h3v.s7.91f62a670966 from=translated src=- shape=2696c7b3 vocab=89187715
-/
theorem integrable_schwartz_mul {r : V → ℂ} (hr : r.HasTemperateGrowth) (g : 𝓢(V, ℂ)) :
    Integrable (fun ξ => g ξ * r ξ) := by
  have h := (smulLeftCLM ℂ r g).integrable (μ := volume)
  have he : (⇑(smulLeftCLM ℂ r g) : V → ℂ) = fun ξ => g ξ * r ξ := by
    funext ξ; rw [smulLeftCLM_apply_apply hr, smul_eq_mul, mul_comm]
  rwa [he] at h

/--
@isnad1 id=eq.0h4v.s9.9102c767ad23 from=translated src=- shape=9d7692a0 vocab=8622a4fd
-/
theorem dual_Mr (a : V) (g : 𝓢(V, ℂ)) (r : V → ℂ) :
    ∫ ξ, Mr a g ξ * r ξ = ∫ ξ, g ξ * (linC a ξ * r ξ) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  change Mr a g ξ * r ξ = g ξ * (linC a ξ * r ξ)
  rw [Mr_apply_apply, linC_apply]; ring

/--
@isnad1 id=eq.1h4v.s10.a36e9308f50a from=translated src=- shape=bdabd93a vocab=5c208d7f
-/
theorem dual_Dd (a : V) (g : 𝓢(V, ℂ)) {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    ∫ ξ, Dd a g ξ * r ξ = ∫ ξ, g ξ * (-fderiv ℝ r ξ a) := by
  have e1 : (fun ξ => Dd a g ξ * r ξ) = fun ξ => r ξ * fderiv ℝ (⇑g) ξ a := by
    funext ξ; rw [Dd_apply_apply]; ring
  rw [e1, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, ← integral_neg]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    change -(fderiv ℝ r ξ a * g ξ) = g ξ * -fderiv ℝ r ξ a
    ring
  · have := integrable_schwartz_mul (hasTemperateGrowth_fderiv_apply hr a) g
    simpa [mul_comm] using this
  · have := integrable_schwartz_mul hr (Dd a g)
    simpa [mul_comm, Dd_apply_apply] using this
  · have := integrable_schwartz_mul hr g
    simpa [mul_comm] using this
  · exact fun x _ => (hr.1.differentiable (by simp)).differentiableAt
  · exact fun x _ => g.differentiableAt

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
variable (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V)

def ChatT (i : ι) (k : κ) (r : V → ℂ) : V → ℂ := fun ξ =>
  cst v b i k * r ξ + (-(2 * π * Complex.I))⁻¹ * (-fderiv ℝ r ξ (avec B b i k))

/--
@isnad1 id=hastempe.1h9v.s7.652aa403b5e2 from=translated src=- shape=23400003 vocab=0fbd8f8a
-/
theorem hasTemperateGrowth_ChatT (i : ι) (k : κ) {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    (ChatT B v b i k r).HasTemperateGrowth := by
  unfold ChatT
  have h1 : (fun ξ => cst v b i k * r ξ).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hr
  have h2 : (fun ξ => (-(2 * π * Complex.I))⁻¹ * (-fderiv ℝ r ξ (avec B b i k))).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul (hasTemperateGrowth_fderiv_apply hr _).neg
  exact h1.add h2

/--
@isnad1 id=eq.1h10v.s9.0f1d30ba2a7e from=translated src=- shape=3a67a964 vocab=0131adc2
-/
theorem dual_Chat (i : ι) (k : κ) (g : 𝓢(V, ℂ)) {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    ∫ ξ, Chat B v b i k g ξ * r ξ = ∫ ξ, g ξ * ChatT B v b i k r ξ := by
  have hI1 := integrable_schwartz_mul hr g
  have hI2 := integrable_schwartz_mul hr (Dd (avec B b i k) g)
  have hI3 := integrable_schwartz_mul (hasTemperateGrowth_fderiv_apply hr (avec B b i k)).neg g
  have lhs : (fun ξ => Chat B v b i k g ξ * r ξ) = fun ξ =>
      cst v b i k * (g ξ * r ξ) + (-(2 * π * Complex.I))⁻¹ * (Dd (avec B b i k) g ξ * r ξ) := by
    funext ξ
    simp only [Chat, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  have rhs : (fun ξ => g ξ * ChatT B v b i k r ξ) = fun ξ =>
      cst v b i k * (g ξ * r ξ) + (-(2 * π * Complex.I))⁻¹ * (g ξ * -fderiv ℝ r ξ (avec B b i k)) := by
    funext ξ; simp only [ChatT]; ring
  have hI3' : Integrable fun ξ => g ξ * -fderiv ℝ r ξ (avec B b i k) := by simpa using hI3
  rw [lhs, rhs, integral_add (hI1.const_mul _) (hI2.const_mul _),
    integral_add (hI1.const_mul _) (hI3'.const_mul _)]
  simp only [integral_const_mul]
  rw [dual_Dd _ _ hr]

def LapHatT (r : V → ℂ) : V → ℂ := fun ξ =>
  ∑ i, ∑ k, ∑ l, (2 * π * Complex.I) ^ 2 *
    (linC (b l) ξ * (linC (b k) ξ * ChatT B v b i l (ChatT B v b i k r) ξ))

/--
@isnad1 id=hastempe.1h7v.s7.f6fb42cdc4ad from=translated src=- shape=32f81afe vocab=eccb4144
-/
theorem hasTemperateGrowth_LapHatT {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    (LapHatT B v b r).HasTemperateGrowth := by
  unfold LapHatT
  refine Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun k _ =>
    Function.HasTemperateGrowth.sum fun l _ => ?_
  refine (Function.HasTemperateGrowth.const _).mul ?_
  exact hasTemperateGrowth_linC_mul (hasTemperateGrowth_linC_mul
    (hasTemperateGrowth_ChatT B v b i l (hasTemperateGrowth_ChatT B v b i k hr)) (b k)) (b l)

/--
@isnad1 id=eq.1h8v.s9.efbf94a8fd38 from=translated src=- shape=5932d898 vocab=f341188e
-/
theorem dual_LapHat (g : 𝓢(V, ℂ)) {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    ∫ ξ, LapHat B v b g ξ * r ξ = ∫ ξ, g ξ * LapHatT B v b r ξ := by

  have lhs : (fun ξ => LapHat B v b g ξ * r ξ) = fun ξ => ∑ i, ∑ k, ∑ l,
      (2 * π * Complex.I) ^ 2 * ((Chat B v b i k (Chat B v b i l (Mr (b k) (Mr (b l) g)))) ξ * r ξ) := by
    funext ξ
    simp only [LapHat, sum_apply, ContinuousLinearMap.comp_apply,
      smul_apply, sum_apply, smul_apply, smul_eq_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  have rhs : (fun ξ => g ξ * LapHatT B v b r ξ) = fun ξ => ∑ i, ∑ k, ∑ l,
      (2 * π * Complex.I) ^ 2 * (g ξ * (linC (b l) ξ * (linC (b k) ξ *
        ChatT B v b i l (ChatT B v b i k r) ξ))) := by
    funext ξ
    simp only [LapHatT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  have hTl : ∀ i k l, Integrable (fun ξ => (2 * π * Complex.I) ^ 2 *
      ((Chat B v b i k (Chat B v b i l (Mr (b k) (Mr (b l) g)))) ξ * r ξ)) := fun i k l =>
    (integrable_schwartz_mul hr _).const_mul _
  have hTr : ∀ i k l, Integrable (fun ξ => (2 * π * Complex.I) ^ 2 * (g ξ * (linC (b l) ξ *
      (linC (b k) ξ * ChatT B v b i l (ChatT B v b i k r) ξ)))) := fun i k l =>
    (integrable_schwartz_mul (hasTemperateGrowth_linC_mul (hasTemperateGrowth_linC_mul
      (hasTemperateGrowth_ChatT B v b i l (hasTemperateGrowth_ChatT B v b i k hr)) (b k)) (b l)) g).const_mul _
  rw [lhs, rhs]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => hTl i k l,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => hTr i k l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hTl i k l,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hTr i k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hTl i k l, integral_finsetSum _ fun l _ => hTr i k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have h1 := hasTemperateGrowth_ChatT B v b i k hr
  have h2 := hasTemperateGrowth_ChatT B v b i l h1
  rw [dual_Chat B v b i k _ hr, dual_Chat B v b i l _ h1, dual_Mr, dual_Mr]

/--
@isnad1 id=eq.1h9v.s9.56bc01ff3e65 from=translated src=- shape=700d83c3 vocab=2682a71f
-/
theorem dual_LapHat_iterate (m : ℕ) (g : 𝓢(V, ℂ)) {r : V → ℂ} (hr : r.HasTemperateGrowth) :
    ∫ ξ, ((LapHat B v b)^[m] g) ξ * r ξ = ∫ ξ, g ξ * ((LapHatT B v b)^[m] r) ξ := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, dual_LapHat B v b _ hr]
    exact ih (hasTemperateGrowth_LapHatT B v b hr)

end Duality

section Realize

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
variable (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V)

/--
@isnad1 id=eq.2h3v.s8.03d5c993b676 from=translated src=- shape=ddd0e71e vocab=52eac0fc
-/
theorem flip_fun {φ ψ : V → ℂ} (hφ : Integrable φ) (hψ : Integrable ψ) :
    ∫ ξ, 𝓕 φ ξ * ψ ξ = ∫ x, φ x * 𝓕 ψ x := by
  have h__af := (VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ V) continuous_fourierChar continuous_inner hφ hψ)
  simp at h__af
  exact h__af

/--
@isnad1 id=eq.0h2v.s8.07de5529df25 from=translated src=- shape=3236cd95 vocab=dc35d71a
-/
theorem integral_fourier_eq_apply_zero (f : 𝓢(V, ℂ)) : ∫ ξ, 𝓕 f ξ = f 0 := by
  have h1 : (𝓕⁻ (𝓕 f)) 0 = f 0 := by rw [fourierInv_fourier_eq]
  rw [← h1, fourierInv_apply_eq, compCLMOfContinuousLinearEquiv_apply]
  simp only [Function.comp_apply]
  rw [show ((LinearIsometryEquiv.neg ℝ (E := V)).toContinuousLinearEquiv : V → V) 0 = 0 from map_zero _]
  simp only [fourier_coe]
  rw [Real.fourier_eq]
  simp

/--
@isnad1 id=eq.3h9v.s10.3e5eeb94ec00 from=translated src=- shape=f7750a5c vocab=e0ac75b0
-/
theorem realize (m : ℕ) {r : V → ℂ} (hr : r.HasTemperateGrowth) (hri : Integrable r)
    (he : Integrable (fun ξ => ((LapHatT B v b)^[m] r) ξ - 1)) (f : 𝓢(V, ℂ)) :
    f 0 = (∫ x, ((LapS B v b)^[m] f) x * 𝓕 r x) +
      ∫ x, f x * (-𝓕 (fun ξ => ((LapHatT B v b)^[m] r) ξ - 1) x) := by
  set g : 𝓢(V, ℂ) := (LapS B v b)^[m] f with hg
  set e : V → ℂ := fun ξ => ((LapHatT B v b)^[m] r) ξ - 1 with he_def

  have h1 : (∫ x, g x * 𝓕 r x) = ∫ ξ, 𝓕 (⇑g) ξ * r ξ := (flip_fun g.integrable hri).symm

  have h2 : 𝓕 (⇑g) = ⇑((LapHat B v b)^[m] (𝓕 f)) := by
    rw [← fourier_coe, hg, fourier_LapS_iterate]

  have h3 := dual_LapHat_iterate B v b m (𝓕 f) hr

  have h4 : (fun ξ => (𝓕 f) ξ * ((LapHatT B v b)^[m] r) ξ) = fun ξ => (𝓕 f) ξ + (𝓕 f) ξ * e ξ := by
    funext ξ; simp only [he_def]; ring
  have hbdd : ∃ C, ∀ ξ, ‖(𝓕 f) ξ‖ ≤ C := by
    exact ⟨‖(𝓕 f).toBoundedContinuousFunction‖, fun ξ => by
      have h__af := BoundedContinuousFunction.norm_coe_le_norm (𝓕 f).toBoundedContinuousFunction ξ
      simp at h__af
      exact h__af⟩
  have hI : Integrable (fun ξ => (𝓕 f) ξ * e ξ) := by
    obtain ⟨C, hC⟩ := hbdd
    exact he.bdd_mul (𝓕 f).continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have h5 : (∫ ξ, (𝓕 f) ξ * ((LapHatT B v b)^[m] r) ξ) = f 0 + ∫ ξ, (𝓕 f) ξ * e ξ := by
    rw [h4, integral_add (𝓕 f).integrable hI, integral_fourier_eq_apply_zero]

  have h6 : (∫ ξ, (𝓕 f) ξ * e ξ) = ∫ x, f x * 𝓕 e x := by
    have := flip_fun f.integrable he
    rw [← fourier_coe] at this
    exact this
  have h7 : (∫ x, f x * (-𝓕 e x)) = -∫ x, f x * 𝓕 e x := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change f x * -𝓕 e x = -(f x * 𝓕 e x); ring
  rw [h7, h1, h2, h3, h5, h6]
  ring

end Realize

section ClosedForm

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
variable (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V)

/--
@isnad1 id=eq.1h11v.s11.cfeb035d289b from=translated src=- shape=5dff7bf5 vocab=53cb06ce
-/
theorem fderiv_ChatT_apply (i : ι) (k : κ) {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) (ξ w : V) :
    fderiv ℝ (ChatT B v b i k r) ξ w =
      cst v b i k * fderiv ℝ r ξ w +
        (-(2 * π * Complex.I))⁻¹ * (-fderiv ℝ (fderiv ℝ r) ξ w (avec B b i k)) := by
  have hd : Differentiable ℝ r := hr.differentiable (by simp)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ r) := (contDiff_infty_iff_fderiv.mp hr).2
  have hd1 : DifferentiableAt ℝ (fderiv ℝ r) ξ := (h1.differentiable (by simp)).differentiableAt
  have hA : HasFDerivAt r (fderiv ℝ r ξ) ξ := hd.differentiableAt.hasFDerivAt
  have hB : HasFDerivAt (fun z => fderiv ℝ r z (avec B b i k))
      ((fderiv ℝ r ξ).comp (0 : V →L[ℝ] V) + (fderiv ℝ (fderiv ℝ r) ξ).flip (avec B b i k)) ξ :=
    hd1.hasFDerivAt.clm_apply (hasFDerivAt_const (avec B b i k) ξ)
  have hC : HasFDerivAt (ChatT B v b i k r)
      (cst v b i k • fderiv ℝ r ξ + (-(2 * π * Complex.I))⁻¹ •
        -((fderiv ℝ r ξ).comp (0 : V →L[ℝ] V) + (fderiv ℝ (fderiv ℝ r) ξ).flip (avec B b i k))) ξ := by
    have := (hA.const_mul (cst v b i k)).add ((hB.neg).const_mul ((-(2 * π * Complex.I))⁻¹))
    exact this
  rw [hC.fderiv]
  simp only [add_apply, smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]

/--
@isnad1 id=contdiff.1h9v.s7.a72a20db5b20 from=translated src=- shape=f34d7e0d vocab=dbc56031
-/
theorem contDiff_ChatT (i : ι) (k : κ) {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) :
    ContDiff ℝ (⊤ : ℕ∞) (ChatT B v b i k r) := by
  unfold ChatT
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => fderiv ℝ r ξ (avec B b i k)) :=
    ((contDiff_infty_iff_fderiv.mp hr).2).clm_apply contDiff_const
  exact (contDiff_const.mul hr).add (contDiff_const.mul h1.neg)

/--
@isnad1 id=eq.1h11v.s11.33c9a30e055d from=translated src=- shape=ee5db822 vocab=d9592c9a
-/
theorem ChatT_ChatT_apply (i : ι) (k l : κ) {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) (ξ : V) :
    ChatT B v b i l (ChatT B v b i k r) ξ =
      cst v b i l * cst v b i k * r ξ
        - (-(2 * π * Complex.I))⁻¹ * cst v b i l * fderiv ℝ r ξ (avec B b i k)
        - (-(2 * π * Complex.I))⁻¹ * cst v b i k * fderiv ℝ r ξ (avec B b i l)
        + (-(2 * π * Complex.I))⁻¹ ^ 2 * fderiv ℝ (fderiv ℝ r) ξ (avec B b i l) (avec B b i k) := by
  change cst v b i l * ChatT B v b i k r ξ +
      (-(2 * π * Complex.I))⁻¹ * (-fderiv ℝ (ChatT B v b i k r) ξ (avec B b i l)) = _
  rw [fderiv_ChatT_apply B v b i k hr ξ (avec B b i l)]
  simp only [ChatT]
  ring

/--
@isnad1 id=eq.0h7v.s7.8b98ad540c49 from=translated src=- shape=799e352a vocab=1c837a82
-/
theorem sum_linC_mul_cst (i : ι) (ξ : V) : ∑ k, linC (b k) ξ * cst v b i k = ((⟪ξ, v i⟫_ℝ : ℝ) : ℂ) := by
  simp only [linC, cst]
  rw [← b.sum_inner_mul_inner ξ (v i)]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm (b k) (v i)]

/--
@isnad1 id=eq.0h7v.s11.2100d4a4eed4 from=translated src=- shape=89ee2e91 vocab=9f95b4f2
-/
theorem sum_inner_smul_avec (i : ι) (ξ : V) : ∑ k, ⟪ξ, b k⟫_ℝ • avec B b i k = ContinuousLinearMap.adjoint (B i) ξ := by
  simp only [avec]
  have : ∑ k, ⟪ξ, b k⟫_ℝ • ContinuousLinearMap.adjoint (B i) (b k) =
      ContinuousLinearMap.adjoint (B i) (∑ k, ⟪ξ, b k⟫_ℝ • b k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul]
  rw [this]
  congr 1
  conv_rhs => rw [← b.sum_repr' ξ]
  exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]

/--
@isnad1 id=eq.0h8v.s11.94e9553b8b3a from=translated src=- shape=b8706c5b vocab=7f7c992b
-/
theorem sum_linC_mul_clm (i : ι) (ξ : V) (L : V →L[ℝ] ℂ) :
    ∑ k, linC (b k) ξ * L (avec B b i k) = L (ContinuousLinearMap.adjoint (B i) ξ) := by
  rw [← sum_inner_smul_avec B b i ξ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, linC_apply, Complex.real_smul]

/--
@isnad1 id=eq.0h8v.s13.95d04533bcdd from=translated src=- shape=5c262604 vocab=7f7c992b
-/
theorem sum_sum_linC_mul_bilin (i : ι) (ξ : V) (L : V →L[ℝ] V →L[ℝ] ℂ) :
    ∑ k, ∑ l, linC (b l) ξ * (linC (b k) ξ * L (avec B b i l) (avec B b i k)) =
      L (ContinuousLinearMap.adjoint (B i) ξ) (ContinuousLinearMap.adjoint (B i) ξ) := by
  have h1 : ∀ l, ∑ k, linC (b k) ξ * L (avec B b i l) (avec B b i k) =
      L (avec B b i l) (ContinuousLinearMap.adjoint (B i) ξ) := fun l =>
    sum_linC_mul_clm B b i ξ (L (avec B b i l))
  have h2 : ∑ l, linC (b l) ξ * L (avec B b i l) (ContinuousLinearMap.adjoint (B i) ξ) =
      L (ContinuousLinearMap.adjoint (B i) ξ) (ContinuousLinearMap.adjoint (B i) ξ) := by
    have := sum_linC_mul_clm B b i ξ (L.flip (ContinuousLinearMap.adjoint (B i) ξ))
    simpa only [ContinuousLinearMap.flip_apply] using this
  rw [← h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← h1 l, Finset.mul_sum]

/--
@isnad1 id=eq.0h5v.s6.9c33023c7ca2 from=translated src=- shape=68b2bb83 vocab=5903f063
-/
theorem dsum1 (F G : κ → ℂ) (c X : ℂ) :
    ∑ k, ∑ l, c * (F l * G k * X) = c * ((∑ l, F l) * (∑ k, G k) * X) := by
  simp only [Finset.sum_mul, Finset.mul_sum]

/--
@isnad1 id=eq.0h5v.s6.dd5ba2cf22c8 from=translated src=- shape=f821d606 vocab=5903f063
-/
theorem dsum2 (F H : κ → ℂ) (c d : ℂ) :
    ∑ k, ∑ l, c * (d * (F l * H k)) = c * (d * ((∑ l, F l) * (∑ k, H k))) := by
  simp only [Finset.sum_mul, Finset.mul_sum]

/--
@isnad1 id=eq.0h5v.s6.5600f7d9087b from=translated src=- shape=5605b6d2 vocab=5903f063
-/
theorem dsum3 (F H : κ → ℂ) (c d : ℂ) :
    ∑ k, ∑ l, c * (d * (F k * H l)) = c * (d * ((∑ k, F k) * (∑ l, H l))) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h4v.s6.06ff8cbe5efe from=translated src=- shape=3eb60571 vocab=5903f063
-/
theorem dsum4 (T : κ → κ → ℂ) (c d : ℂ) :
    ∑ k, ∑ l, c * (d * T k l) = c * (d * ∑ k, ∑ l, T k l) := by
  simp only [Finset.mul_sum]

/--
@isnad1 id=eq.1h8v.s13.accccd070a8f from=translated src=- shape=760f51c1 vocab=10f725b6
-/
theorem LapHatT_apply {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) (ξ : V) :
    LapHatT B v b r ξ = ∑ i,
      (fderiv ℝ (fderiv ℝ r) ξ (ContinuousLinearMap.adjoint (B i) ξ) (ContinuousLinearMap.adjoint (B i) ξ)
        + (4 * π * Complex.I) * ((⟪ξ, v i⟫_ℝ : ℝ) : ℂ) * fderiv ℝ r ξ (ContinuousLinearMap.adjoint (B i) ξ)
        - (4 * π ^ 2 : ℂ) * ((⟪ξ, v i⟫_ℝ : ℝ) : ℂ) ^ 2 * r ξ) := by
  unfold LapHatT
  refine Finset.sum_congr rfl fun i _ => ?_

  have hexp : ∀ k l, linC (b l) ξ * (linC (b k) ξ * ChatT B v b i l (ChatT B v b i k r) ξ) =
      (linC (b l) ξ * cst v b i l) * (linC (b k) ξ * cst v b i k) * r ξ
      - (-(2 * π * Complex.I))⁻¹ * ((linC (b l) ξ * cst v b i l) * (linC (b k) ξ * fderiv ℝ r ξ (avec B b i k)))
      - (-(2 * π * Complex.I))⁻¹ * ((linC (b k) ξ * cst v b i k) * (linC (b l) ξ * fderiv ℝ r ξ (avec B b i l)))
      + (-(2 * π * Complex.I))⁻¹ ^ 2 *
          (linC (b l) ξ * (linC (b k) ξ * fderiv ℝ (fderiv ℝ r) ξ (avec B b i l) (avec B b i k))) := by
    intro k l
    rw [ChatT_ChatT_apply B v b i k l hr ξ]
    ring
  simp_rw [hexp]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [dsum1 (fun l => linC (b l) ξ * cst v b i l) (fun k => linC (b k) ξ * cst v b i k),
    dsum2 (fun l => linC (b l) ξ * cst v b i l) (fun k => linC (b k) ξ * fderiv ℝ r ξ (avec B b i k)),
    dsum3 (fun k => linC (b k) ξ * cst v b i k) (fun l => linC (b l) ξ * fderiv ℝ r ξ (avec B b i l)),
    dsum4 (fun k l => linC (b l) ξ * (linC (b k) ξ * fderiv ℝ (fderiv ℝ r) ξ (avec B b i l) (avec B b i k)))]
  rw [sum_linC_mul_cst v b i ξ, sum_linC_mul_clm B b i ξ (fderiv ℝ r ξ),
    sum_sum_linC_mul_bilin B b i ξ (fderiv ℝ (fderiv ℝ r) ξ)]
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπ : (2 * ↑π * Complex.I) ^ 2 = -(4 * π ^ 2 : ℂ) := by
    rw [mul_pow, mul_pow, Complex.I_sq]; ring
  have hI : (-(2 * ↑π * Complex.I))⁻¹ = Complex.I / (2 * π) := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    rw [Complex.I_sq]; ring
  rw [hπ, hI]
  field_simp
  rw [Complex.I_sq]
  ring

end ClosedForm

section Glue

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

def cardOp (B : ι → V →L[ℝ] V) (v : ι → V) : (V → ℂ) → (V → ℂ) :=
  fun G y => ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => B i y + v i)

def linOp (A : ι → V →L[ℝ] V) : (V → ℂ) → (V → ℂ) :=
  fun (G : V → ℂ) (y : V) => ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y)

def symOp (B : ι → V →L[ℝ] V) (v : ι → V) : (V → ℂ) → (V → ℂ) :=
  fun (g : V → ℂ) (η : V) => ∑ i,
    (iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) +
      (4 * Real.pi * Complex.I) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
        fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η) -
      (4 * Real.pi ^ 2 : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2 * g η)

/--
@isnad1 id=eq.0h8v.s9.e8203183aca7 from=translated src=- shape=4667d5e6 vocab=e6d175d1
-/
theorem coe_LapS_iterate (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V) (m : ℕ)
    (f : 𝓢(V, ℂ)) : ⇑((LapS B v b)^[m] f) = (cardOp B v)^[m] ⇑f := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    funext y
    rw [LapS_apply, ← ih]
    rfl

/--
@isnad1 id=eq.0h5v.s8.f1c45a297ed5 from=translated src=- shape=0264603d vocab=deb25c26
-/
theorem cardOp_translate (A : ι → V →L[ℝ] V) (x₀ : V) (G : V → ℂ) :
    cardOp A (fun i => A i x₀) (fun z => G (z + x₀)) = fun y => linOp A G (y + x₀) := by
  funext y
  simp only [cardOp, linOp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_comp_add_right]
  congr 1
  funext j
  rw [map_add]

/--
@isnad1 id=eq.0h6v.s8.4cf75be3c322 from=translated src=- shape=de0a9545 vocab=3f014f35
-/
theorem cardOp_iterate_translate (A : ι → V →L[ℝ] V) (x₀ : V) (m : ℕ) (G : V → ℂ) :
    (cardOp A (fun i => A i x₀))^[m] (fun z => G (z + x₀)) = fun y => (linOp A)^[m] G (y + x₀) := by
  induction m generalizing G with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cardOp_translate, ih]

/--
@isnad1 id=contdiff.0h2v.s6.c109c1d90be2 from=translated src=- shape=aa8f6018 vocab=5f585216
-/
theorem contDiff_linC (a : V) : ContDiff ℝ (⊤ : ℕ∞) (linC a) := (hasTemperateGrowth_linC a).1

/--
@isnad1 id=contdiff.1h7v.s7.6ab2da939664 from=translated src=- shape=885be01f vocab=b588f804
-/
theorem contDiff_LapHatT (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V) {g : V → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (LapHatT B v b g) := by
  unfold LapHatT
  refine ContDiff.sum fun i _ => ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_
  refine contDiff_const.mul ((contDiff_linC (b l)).mul ((contDiff_linC (b k)).mul ?_))
  exact contDiff_ChatT B v b i l (contDiff_ChatT B v b i k hg)

/--
@isnad1 id=eq.1h7v.s7.0929023bf674 from=translated src=- shape=69d4bb35 vocab=8e412911
-/
theorem LapHatT_eq_symOp (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V) {g : V → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : LapHatT B v b g = symOp B v g := by
  funext ξ
  rw [LapHatT_apply B v b hg ξ]
  simp only [symOp, iteratedFDeriv_two_apply]

/--
@isnad1 id=and.1h8v.s8.472d2a5eb12d from=translated src=- shape=2eced7ac vocab=c08e69b3
-/
theorem LapHatT_iterate_eq (B : ι → V →L[ℝ] V) (v : ι → V) (b : OrthonormalBasis κ ℝ V) (m : ℕ)
    {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) :
    (LapHatT B v b)^[m] r = (symOp B v)^[m] r ∧ ContDiff ℝ (⊤ : ℕ∞) ((LapHatT B v b)^[m] r) := by
  induction m with
  | zero => exact ⟨rfl, hr⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨?_, contDiff_LapHatT B v b ih.2⟩
    rw [LapHatT_eq_symOp B v b ih.2, ih.1]

/--
@isnad1 id=hastempe.2h3v.s8.63e9776a5dc0 from=translated src=- shape=ebb6efa4 vocab=583abf73
-/
theorem hasTemperateGrowth_of_bounds {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) (m : ℕ)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ))) :
    r.HasTemperateGrowth := by
  refine ⟨hr, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hb n
  have hC0 : 0 ≤ C := by
    have h := hC 0
    rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨0, C, fun ξ => (hC ξ).trans ?_⟩
  rw [pow_zero, mul_one]
  have h1 : (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ξ])
      (by have : (0 : ℝ) ≤ 2 * m + n := by positivity
          linarith)
  exact mul_le_of_le_one_right hC0 h1

/--
@isnad1 id=integrab.3h3v.s8.0e99ff260be2 from=translated src=- shape=79d91ade vocab=fbb90c37
-/
theorem integrable_of_bounds {r : V → ℂ} (hr : ContDiff ℝ (⊤ : ℕ∞) r) (m : ℕ)
    (hm : Module.finrank ℝ V < 2 * m)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ))) :
    Integrable r := by
  obtain ⟨C, hC⟩ := hb 0
  have hm' : (Module.finrank ℝ V : ℝ) < (2 * m : ℝ) := by exact_mod_cast hm
  have hint := (integrable_one_add_norm (E := V) (μ := volume) hm').const_mul C
  refine hint.mono' hr.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have h := hC ξ
  rw [norm_iteratedFDeriv_zero] at h
  simpa using h

end Glue

section Main

variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=ex.2h5v.s9.99941d811eb4 from=translated src=- shape=f97fd72b vocab=478e117f
-/
theorem main (A : ι → V →L[ℝ] V) (x₀ : V)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ u w : V → ℂ, Continuous u ∧ Continuous w ∧ ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ ∧
      ∀ F : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((linOp A)^[m] F) x * u x) + ∫ x, F x * w x := by

  obtain ⟨r, hr, hb, he⟩ :=
    LocalParametrix.exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
      A (fun i => A i x₀) hA m hm
  let b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V
  have hLe := (LapHatT_iterate_eq A (fun i => A i x₀) b m hr).1
  have he' : Integrable (fun ξ => ((LapHatT A (fun i => A i x₀) b)^[m] r) ξ - 1) := by
    rw [hLe]; exact he
  have hrT := hasTemperateGrowth_of_bounds hr m hb
  have hri := integrable_of_bounds hr m hm hb

  have hm' : (Module.finrank ℝ V : ℝ) < (2 * m : ℝ) := by exact_mod_cast hm
  obtain ⟨hcont, hsmooth⟩ :=
    LocalParametrix.continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le
      r hr (2 * m) hm' hb
  set e : V → ℂ := fun ξ => ((LapHatT A (fun i => A i x₀) b)^[m] r) ξ - 1 with he_def
  have hecont : Continuous (𝓕 e) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ he'
  refine ⟨fun x => 𝓕 r (x - x₀), fun x => -𝓕 e (x - x₀),
    hcont.comp (continuous_id.sub continuous_const),
    (hecont.comp (continuous_id.sub continuous_const)).neg, ?_, ?_⟩
  · refine hsmooth.comp ((contDiff_id.sub contDiff_const).contDiffOn) ?_
    intro x hx h0
    exact hx (sub_eq_zero.mp h0)
  · intro F hF hFc
    have hF₀ : ContDiff ℝ (⊤ : ℕ∞) (fun z => F (z + x₀)) := hF.comp (contDiff_id.add contDiff_const)
    have hF₀c : HasCompactSupport (fun z => F (z + x₀)) := hFc.comp_homeomorph (Homeomorph.addRight x₀)
    let f : 𝓢(V, ℂ) := hF₀c.toSchwartzMap hF₀
    have hf : (⇑f : V → ℂ) = fun z => F (z + x₀) := rfl
    have h1 := realize A (fun i => A i x₀) b m hrT hri he' f
    have hf0 : f 0 = F x₀ := by
      change (fun z => F (z + x₀)) 0 = F x₀
      simp only [zero_add]
    rw [hf0, coe_LapS_iterate, hf, cardOp_iterate_translate] at h1
    have t1 : (∫ x, (fun y => (linOp A)^[m] F (y + x₀)) x * 𝓕 r x) =
        ∫ y, (linOp A)^[m] F y * 𝓕 r (y - x₀) := by
      have := integral_add_right_eq_self (μ := (volume : Measure V))
        (fun y => (linOp A)^[m] F y * 𝓕 r (y - x₀)) x₀
      simp only [add_sub_cancel_right] at this
      exact this
    have t2 : (∫ x, (fun z => F (z + x₀)) x * -𝓕 e x) = ∫ y, F y * -𝓕 e (y - x₀) := by
      have := integral_add_right_eq_self (μ := (volume : Measure V))
        (fun y => F y * -𝓕 e (y - x₀)) x₀
      simp only [add_sub_cancel_right] at this
      exact this
    rw [h1, t1, t2]

end Main

end R4P1Engine

end

open MeasureTheory Topology in
/--
@isnad1 id=ex.2h5v.s10.8db61330a754 from=translated src=- shape=24764068 vocab=ab393d2a
-/
theorem solution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {ι : Type*} [Fintype ι] (A : ι → V →L[ℝ] V) (x₀ : V)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ u w : V → ℂ, Continuous u ∧ Continuous w ∧ ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ ∧
      ∀ F : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((fun (G : V → ℂ) (y : V) =>
                  ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y))^[m] F) x * u x) +
          ∫ x, F x * w x :=
  R4P1Engine.main A x₀ hA m hm
