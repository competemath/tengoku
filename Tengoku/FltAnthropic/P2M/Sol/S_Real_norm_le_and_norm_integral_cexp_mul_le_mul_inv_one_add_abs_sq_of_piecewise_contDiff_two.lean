import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two

set_option autoImplicit false

open MeasureTheory Real

namespace R4WinKink

noncomputable def cst (ξ : ℝ) : ℂ := -(2 * Real.pi * Complex.I * ξ)

/--
@isnad1 id=eq.0h2v.s6.53835df74ffc from=translated src=- shape=487c1f02 vocab=0bc8ad9b
-/
theorem kernel_eq (ξ x : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x : ℝ) : ℂ))) = Complex.exp (cst ξ * x) := by
  unfold cst
  congr 1
  push_cast
  ring

/--
@isnad1 id=eq.0h2v.s4.16573f8d99a1 from=translated src=- shape=3788a8b9 vocab=d0ab4f77
-/
theorem norm_exp_cst (ξ x : ℝ) : ‖Complex.exp (cst ξ * x)‖ = 1 := by
  rw [show cst ξ * x = ((-(2 * Real.pi * ξ * x) : ℝ) : ℂ) * Complex.I by
    unfold cst; push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/--
@isnad1 id=ne.1h1v.s4.fe90ff0da871 from=translated src=- shape=20a1293d vocab=5c4062ba
-/
theorem cst_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) : cst ξ ≠ 0 := by
  unfold cst
  simp [Real.pi_ne_zero, Complex.I_ne_zero, hξ]

/--
@isnad1 id=eq.0h1v.s6.4eaae86de0da from=translated src=- shape=3ab82757 vocab=6630683c
-/
theorem norm_cst_sq (ξ : ℝ) : ‖cst ξ ^ 2‖ = (2 * Real.pi * |ξ|) ^ 2 := by
  rw [norm_pow]
  unfold cst
  simp [Complex.norm_real, abs_of_pos Real.pi_pos]

/--
@isnad1 id=continuo.0h1v.s5.d789f0818c18 from=translated src=- shape=64e91efb vocab=6903ddda
-/
theorem continuous_exp_cst (c : ℂ) : Continuous fun y : ℝ => Complex.exp (c * y) := by
  fun_prop

/--
@isnad1 id=hasderiv.1h2v.s6.5332cfad04ec from=translated src=- shape=fe4debe6 vocab=ba18eeda
-/
theorem hasDerivAt_exp_div (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
  have h1 : HasDerivAt (fun w : ℂ => c * w) c (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul c
  have h2 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := h1.comp_ofReal
  have h3 : HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * x) * c) x := h2.cexp
  have h4 := h3.div_const c
  convert h4 using 1
  · rfl
  field_simp

/--
@isnad1 id=eq.3h4v.s8.481fc16c9e01 from=translated src=- shape=9219f95c vocab=58fd0c8b
-/
theorem ibp_once (u : ℝ → ℂ) (hu : Differentiable ℝ u) (hu' : Continuous (deriv u))
    (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, u x * Complex.exp (c * x) =
      (u b * Complex.exp (c * b) - u a * Complex.exp (c * a)) / c
        - c⁻¹ * ∫ x in a..b, deriv u x * Complex.exp (c * x) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := u) (v := fun y : ℝ => Complex.exp (c * y) / c) (u' := deriv u)
    (v' := fun y : ℝ => Complex.exp (c * y)) (a := a) (b := b)
    (fun x _ => (hu x).hasDerivAt) (fun x _ => hasDerivAt_exp_div c hc x)
    (hu'.intervalIntegrable _ _) ((continuous_exp_cst c).intervalIntegrable _ _)
  rw [h]
  have h2 : ∫ x in a..b, deriv u x * (Complex.exp (c * x) / c) =
      c⁻¹ * ∫ x in a..b, deriv u x * Complex.exp (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    field_simp
  rw [h2]
  field_simp

/--
@isnad1 id=eq.0h1v.s7.5399fe1b6e3a from=translated src=- shape=0351daa9 vocab=2fbdde00
-/
theorem iteratedDeriv_two_eq (h : ℝ → ℂ) : iteratedDeriv 2 h = deriv (deriv h) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/--
@isnad1 id=eq.2h4v.s8.2c470244556b from=translated src=- shape=bb4bee63 vocab=801fa219
-/
theorem ibp_twice (h : ℝ → ℂ) (hh : ContDiff ℝ 2 h) (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, h x * Complex.exp (c * x) =
      (h b * Complex.exp (c * b) - h a * Complex.exp (c * a)) / c
        - (deriv h b * Complex.exp (c * b) - deriv h a * Complex.exp (c * a)) / c ^ 2
        + (c ^ 2)⁻¹ * ∫ x in a..b, iteratedDeriv 2 h x * Complex.exp (c * x) := by
  have hd0 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv h) := by
    have := hh.differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  have hc1 : Continuous (deriv h) := by
    simpa [iteratedDeriv_one] using hh.continuous_iteratedDeriv 1 (by norm_num)
  have hc2 : Continuous (deriv (deriv h)) := by
    have := hh.continuous_iteratedDeriv 2 le_rfl
    rwa [iteratedDeriv_two_eq] at this
  rw [ibp_once h hd0 hc1 c hc a b, ibp_once (deriv h) hd1 hc2 c hc a b, iteratedDeriv_two_eq]
  field_simp
  ring

/--
@isnad1 id=eq.3h4v.s6.8b8ced12a692 from=translated src=- shape=96b49bbc vocab=659f8cb0
-/
theorem iteratedDeriv_eq_zero_of_isOpen {h : ℝ → ℂ} {S : Set ℝ} (hS : IsOpen S)
    (hz : ∀ x ∈ S, h x = 0) (n : ℕ) {x : ℝ} (hx : x ∈ S) : iteratedDeriv n h x = 0 := by
  have hev : h =ᶠ[nhds x] (fun _ => (0 : ℂ)) :=
    Filter.eventually_of_mem (hS.mem_nhds hx) fun y hy => hz y hy
  have h1 := (hev.iteratedDeriv n).self_of_nhds
  rw [h1, iteratedDeriv_const]
  simp

/--
@isnad1 id=eq.5h4v.s7.a75c358855fa from=translated src=- shape=33ec013d vocab=83b1c77e
-/
theorem iteratedDeriv_eq_zero_of_mem_closure {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) {S : Set ℝ}
    (hS : IsOpen S) (hz : ∀ x ∈ S, h x = 0) (n : ℕ) (hn : (n : WithTop ℕ∞) ≤ 2) {x : ℝ}
    (hx : x ∈ closure S) : iteratedDeriv n h x = 0 := by
  have hcont : Continuous (iteratedDeriv n h) := hh.continuous_iteratedDeriv n hn
  have hclosed : IsClosed {y : ℝ | iteratedDeriv n h y = 0} := isClosed_eq hcont continuous_const
  have hsub : S ⊆ {y : ℝ | iteratedDeriv n h y = 0} := fun y hy => iteratedDeriv_eq_zero_of_isOpen hS hz n hy
  exact hclosed.closure_subset_iff.mpr hsub hx

/--
@isnad1 id=and.2h2v.s7.16d4f61017b7 from=translated src=- shape=409635ab vocab=3819f5ab
-/
theorem right_edge {gp : ℝ → ℂ} (hgp : ContDiff ℝ 2 gp) {R : ℝ} (hz : ∀ x, R < x → gp x = 0) :
    gp R = 0 ∧ deriv gp R = 0 := by
  have hcl : R ∈ closure (Set.Ioi R) := by
    rw [closure_Ioi]; exact Set.self_mem_Ici
  have h0 := iteratedDeriv_eq_zero_of_mem_closure hgp isOpen_Ioi (fun x hx => hz x hx) 0 (by norm_num) hcl
  have h1 := iteratedDeriv_eq_zero_of_mem_closure hgp isOpen_Ioi (fun x hx => hz x hx) 1 (by norm_num) hcl
  rw [iteratedDeriv_zero] at h0
  rw [iteratedDeriv_one] at h1
  exact ⟨h0, h1⟩

/--
@isnad1 id=and.2h2v.s7.04d1c4a25e17 from=translated src=- shape=01320af2 vocab=b3a32017
-/
theorem left_edge {gm : ℝ → ℂ} (hgm : ContDiff ℝ 2 gm) {R : ℝ} (hz : ∀ x, x < -R → gm x = 0) :
    gm (-R) = 0 ∧ deriv gm (-R) = 0 := by
  have hcl : -R ∈ closure (Set.Iio (-R)) := by
    rw [closure_Iio]; exact Set.self_mem_Iic
  have h0 := iteratedDeriv_eq_zero_of_mem_closure hgm isOpen_Iio (fun x hx => hz x hx) 0 (by norm_num) hcl
  have h1 := iteratedDeriv_eq_zero_of_mem_closure hgm isOpen_Iio (fun x hx => hz x hx) 1 (by norm_num) hcl
  rw [iteratedDeriv_zero] at h0
  rw [iteratedDeriv_one] at h1
  exact ⟨h0, h1⟩

/--
@isnad1 id=lt.1h2v.s4.744ad95ac8f4 from=translated src=- shape=e3a6d85f vocab=3aa78d74
-/
theorem lt_abs_of_not_mem_Icc {R x : ℝ} (hx : x ∉ Set.Icc (-R) R) : R < |x| := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact lt_abs.mpr (Or.inr (by linarith))
  · exact lt_abs.mpr (Or.inl hx)

/--
@isnad1 id=le.1h2v.s6.6ae84f24fd1e from=translated src=- shape=80766f04 vocab=873430eb
-/
theorem window_le {R x : ℝ} (hx : |x| ≤ R) : (1 : ℝ) ≤ (1 + R) ^ 2 * (1 + |x|)⁻¹ ^ 2 := by
  have h1 : 0 < 1 + |x| := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_left₀ h1.le (by linarith) 2

/--
@isnad1 id=le.1h1v.s6.55d683ea4c56 from=translated src=- shape=3d470433 vocab=31ba0678
-/
theorem window_ge_quarter_of_le_one {ξ : ℝ} (hξ : |ξ| ≤ 1) : (1 : ℝ) / 4 ≤ (1 + |ξ|)⁻¹ ^ 2 := by
  have h1 : 0 < 1 + |ξ| := by positivity
  rw [inv_pow, ← one_div, div_le_div_iff₀ (by norm_num) (by positivity), one_mul, one_mul]
  nlinarith [abs_nonneg ξ]

/--
@isnad1 id=le.1h1v.s6.4b591e1fbcad from=translated src=- shape=4344e28f vocab=873430eb
-/
theorem inv_sq_le_window_of_one_le {ξ : ℝ} (hξ : 1 ≤ |ξ|) : (ξ ^ 2)⁻¹ ≤ 4 * (1 + |ξ|)⁻¹ ^ 2 := by
  have h1 : 0 < 1 + |ξ| := by positivity
  have hξ0 : 0 < ξ ^ 2 := by nlinarith [abs_nonneg ξ, sq_abs ξ]
  rw [inv_pow, show (4:ℝ) * ((1 + |ξ|) ^ 2)⁻¹ = 4 / (1 + |ξ|) ^ 2 from by ring, inv_eq_one_div,
    div_le_div_iff₀ hξ0 (by positivity), one_mul]
  nlinarith [abs_nonneg ξ, sq_abs ξ]

section Pasted

variable {g gm gp : ℝ → ℂ} {R M₀ M₂ J : ℝ}

/--
@isnad1 id=eq.2h3v.s6.a46028633517 from=translated src=- shape=48380b78 vocab=d6248b85
-/
theorem g_eq_ite (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x) :
    g = fun x => if x ≤ 0 then gm x else gp x := by
  funext x
  split_ifs with hx
  · exact hm x hx
  · exact hp x (le_of_lt (lt_of_not_ge hx))

/--
@isnad1 id=continuo.4h3v.s7.0dad4f104106 from=translated src=- shape=4669fb83 vocab=72696356
-/
theorem continuous_g (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x) : Continuous g := by
  rw [g_eq_ite hm hp]
  refine Continuous.if_le hgm.continuous hgp.continuous continuous_id continuous_const ?_
  intro x hx
  rw [← hm x (le_of_eq hx), ← hp x (ge_of_eq hx)]

/--
@isnad1 id=and.4h3v.s7.df9d3244d07a from=translated src=- shape=3fee1f9b vocab=ce9a8128
-/
theorem integrable_and_integral_norm_le (hR : 0 ≤ R) {h : ℝ → ℂ} {M : ℝ} (hc : Continuous h)
    (hh : ∀ x, ‖h x‖ ≤ M) (hz : ∀ x, R < |x| → h x = 0) :
    Integrable h ∧ ∫ x, ‖h x‖ ≤ 2 * R * M := by
  have hbound : ∀ x, ‖h x‖ ≤ Set.indicator (Set.Icc (-R) R) (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hx]; exact hh x
    · rw [Set.indicator_of_notMem hx, hz x (lt_abs_of_not_mem_Icc hx), norm_zero]
  have hind : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => M)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hint : Integrable h :=
    Integrable.mono' hind hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine ⟨hint, ?_⟩
  calc ∫ x, ‖h x‖ ≤ ∫ x, Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => M) x :=
        integral_mono hint.norm hind hbound
    _ = 2 * R * M := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, Real.volume_real_Icc]
        rw [max_eq_left (by linarith)]
        ring

/--
@isnad1 id=le.4h4v.s7.48e87ee8dbb4 from=translated src=- shape=38e9bc64 vocab=dd3cd376
-/
theorem norm_transform_le_L1 (hR : 0 ≤ R) (hc : Continuous g) (hM₀ : ∀ x, ‖g x‖ ≤ M₀)
    (hsupp : ∀ x, R < |x| → g x = 0) (ξ : ℝ) :
    ‖∫ x : ℝ, Complex.exp (cst ξ * x) * g x‖ ≤ 2 * R * M₀ := by
  obtain ⟨hint, hL1⟩ := integrable_and_integral_norm_le hR hc hM₀ hsupp
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_trans (le_of_eq ?_) hL1
  congr 1; ext x
  rw [norm_mul, norm_exp_cst, one_mul]

/--
@isnad1 id=eq.7h5v.s9.9591c760d2e7 from=translated src=- shape=4dde6834 vocab=780988e6
-/
theorem transform_eq_corner (hR : 0 ≤ R) (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x)
    (hsupp : ∀ x, R < |x| → g x = 0) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∫ x : ℝ, Complex.exp (cst ξ * x) * g x =
      (cst ξ ^ 2)⁻¹ * ((deriv gp 0 - deriv gm 0)
        + (∫ x in (-R)..0, iteratedDeriv 2 gm x * Complex.exp (cst ξ * x))
        + (∫ x in (0 : ℝ)..R, iteratedDeriv 2 gp x * Complex.exp (cst ξ * x))) := by
  set c := cst ξ with hcdef
  have hc : c ≠ 0 := cst_ne_zero hξ
  have hgc : Continuous g := continuous_g hgm hgp hm hp
  have hFc : Continuous fun x : ℝ => Complex.exp (c * x) * g x := (continuous_exp_cst c).mul hgc

  have h1 : ∫ x : ℝ, Complex.exp (c * x) * g x = ∫ x in (-R)..R, Complex.exp (c * x) * g x := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hsupp x (lt_abs_of_not_mem_Icc hx), mul_zero]

  have h2 : ∫ x in (-R)..R, Complex.exp (c * x) * g x =
      (∫ x in (-R)..0, Complex.exp (c * x) * g x) + ∫ x in (0 : ℝ)..R, Complex.exp (c * x) * g x :=
    (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _)).symm

  have h3m : ∫ x in (-R)..0, Complex.exp (c * x) * g x = ∫ x in (-R)..0, gm x * Complex.exp (c * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith : -R ≤ 0), Set.mem_Icc] at hx
    rw [hm x hx.2, mul_comm]
  have h3p : ∫ x in (0 : ℝ)..R, Complex.exp (c * x) * g x = ∫ x in (0 : ℝ)..R, gp x * Complex.exp (c * x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hR, Set.mem_Icc] at hx
    rw [hp x hx.1, mul_comm]

  have hzp : ∀ x, R < x → gp x = 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith
    rw [← hp x hx0]
    exact hsupp x (by rw [abs_of_nonneg hx0]; exact hx)
  have hzm : ∀ x, x < -R → gm x = 0 := by
    intro x hx
    have hx0 : x ≤ 0 := by linarith
    rw [← hm x hx0]
    exact hsupp x (by rw [abs_of_nonpos hx0]; linarith)
  obtain ⟨hpR, hp'R⟩ := right_edge hgp hzp
  obtain ⟨hmR, hm'R⟩ := left_edge hgm hzm
  have h00 : gm 0 = gp 0 := by rw [← hm 0 le_rfl, ← hp 0 le_rfl]

  rw [h1, h2, h3m, h3p, ibp_twice gm hgm c hc (-R) 0, ibp_twice gp hgp c hc 0 R, hpR, hp'R, hmR, hm'R,
    h00]
  push_cast
  simp only [mul_zero, Complex.exp_zero, mul_one, zero_mul, sub_zero, zero_sub]
  field_simp
  ring

/--
@isnad1 id=le.10h7v.s9.2851b1d45e2a from=translated src=- shape=f5b86a6b vocab=287316e2
-/
theorem norm_transform_le_of_one_le (hR : 0 ≤ R) (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x)
    (hsupp : ∀ x, R < |x| → g x = 0)
    (hM₂m : ∀ x, x ≤ 0 → ‖iteratedDeriv 2 gm x‖ ≤ M₂)
    (hM₂p : ∀ x, 0 ≤ x → ‖iteratedDeriv 2 gp x‖ ≤ M₂)
    (hJ : ‖deriv gp 0 - deriv gm 0‖ ≤ J) {ξ : ℝ} (hξ1 : 1 ≤ |ξ|) :
    ‖∫ x : ℝ, Complex.exp (cst ξ * x) * g x‖ ≤ (2 * R * M₂ + J) / Real.pi ^ 2 * (1 + |ξ|)⁻¹ ^ 2 := by
  have hξ0 : ξ ≠ 0 := by
    intro h; rw [h, abs_zero] at hξ1; linarith
  have hM₂' : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂p 0 le_rfl)
  have hJ' : 0 ≤ J := (norm_nonneg _).trans hJ
  rw [transform_eq_corner hR hgm hgp hm hp hsupp hξ0, norm_mul, norm_inv, norm_cst_sq]

  have hIm : ‖∫ x in (-R)..0, iteratedDeriv 2 gm x * Complex.exp (cst ξ * x)‖ ≤ M₂ * |0 - (-R)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith : -R ≤ 0), Set.mem_Ioc] at hx
    rw [norm_mul, norm_exp_cst, mul_one]
    exact hM₂m x hx.2
  have hIp : ‖∫ x in (0 : ℝ)..R, iteratedDeriv 2 gp x * Complex.exp (cst ξ * x)‖ ≤ M₂ * |R - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hR, Set.mem_Ioc] at hx
    rw [norm_mul, norm_exp_cst, mul_one]
    exact hM₂p x hx.1.le
  rw [sub_neg_eq_add, zero_add, abs_of_nonneg hR] at hIm
  rw [sub_zero, abs_of_nonneg hR] at hIp
  have hsum : ‖(deriv gp 0 - deriv gm 0)
        + (∫ x in (-R)..0, iteratedDeriv 2 gm x * Complex.exp (cst ξ * x))
        + (∫ x in (0 : ℝ)..R, iteratedDeriv 2 gp x * Complex.exp (cst ξ * x))‖ ≤ J + 2 * R * M₂ := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    linarith
  have hkey : ((2 * Real.pi * |ξ|) ^ 2)⁻¹ * (J + 2 * R * M₂) ≤
      (2 * R * M₂ + J) / Real.pi ^ 2 * (1 + |ξ|)⁻¹ ^ 2 := by
    have h4 := inv_sq_le_window_of_one_le hξ1
    have hC : 0 ≤ (2 * R * M₂ + J) / Real.pi ^ 2 := by positivity
    calc ((2 * Real.pi * |ξ|) ^ 2)⁻¹ * (J + 2 * R * M₂)
        = ((2 * R * M₂ + J) / Real.pi ^ 2) * ((ξ ^ 2)⁻¹ / 4) := by
          rw [← sq_abs ξ]; field_simp; ring
      _ ≤ ((2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC; linarith
  calc ((2 * Real.pi * |ξ|) ^ 2)⁻¹ * ‖(deriv gp 0 - deriv gm 0)
        + (∫ x in (-R)..0, iteratedDeriv 2 gm x * Complex.exp (cst ξ * x))
        + (∫ x in (0 : ℝ)..R, iteratedDeriv 2 gp x * Complex.exp (cst ξ * x))‖
      ≤ ((2 * Real.pi * |ξ|) ^ 2)⁻¹ * (J + 2 * R * M₂) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 * R * M₂ + J) / Real.pi ^ 2 * (1 + |ξ|)⁻¹ ^ 2 := hkey

end Pasted

end R4WinKink

open R4WinKink in

/--
@isnad1 id=and.10h7v.s9.91db1d6ec3a6 from=translated src=- shape=ba1781b2 vocab=b5bf9b25
-/
theorem solution
    (g gm gp : ℝ → ℂ) (R M₀ M₂ J : ℝ) (hR : 0 ≤ R)
    (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x)
    (hsupp : ∀ x, R < |x| → g x = 0)
    (hM₀ : ∀ x, ‖g x‖ ≤ M₀)
    (hM₂m : ∀ x, x ≤ 0 → ‖iteratedDeriv 2 gm x‖ ≤ M₂)
    (hM₂p : ∀ x, 0 ≤ x → ‖iteratedDeriv 2 gp x‖ ≤ M₂)
    (hJ : ‖deriv gp 0 - deriv gm 0‖ ≤ J) :
    (∀ x : ℝ, ‖g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |x|)⁻¹ ^ 2) ∧
    (∀ ξ : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x : ℝ) : ℂ))) * g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2) := by
  have hM₀' : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₂' : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂p 0 le_rfl)
  have hJ' : 0 ≤ J := (norm_nonneg _).trans hJ
  have hA : 0 ≤ M₀ * (1 + R) ^ 2 := by positivity
  have hB : 0 ≤ 8 * R * M₀ := by positivity
  have hC : 0 ≤ (2 * R * M₂ + J) / Real.pi ^ 2 := by positivity
  have hgc : Continuous g := continuous_g hgm hgp hm hp
  refine ⟨fun x => ?_, fun ξ => ?_⟩
  · have hw : 0 ≤ (1 + |x|)⁻¹ ^ 2 := by positivity
    by_cases hx : |x| ≤ R
    · calc ‖g x‖ ≤ M₀ := hM₀ x
        _ ≤ M₀ * ((1 + R) ^ 2 * (1 + |x|)⁻¹ ^ 2) := le_mul_of_one_le_right hM₀' (window_le hx)
        _ = M₀ * (1 + R) ^ 2 * (1 + |x|)⁻¹ ^ 2 := by ring
        _ ≤ (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |x|)⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hw; linarith
    · rw [hsupp x (lt_of_not_ge hx), norm_zero]; positivity
  · have hw : 0 ≤ (1 + |ξ|)⁻¹ ^ 2 := by positivity
    have hker : ∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x : ℝ) : ℂ))) * g x =
        ∫ x : ℝ, Complex.exp (cst ξ * x) * g x := by
      congr 1; ext x; rw [kernel_eq]
    rw [hker]
    by_cases hξ : |ξ| ≤ 1
    · calc ‖∫ x : ℝ, Complex.exp (cst ξ * x) * g x‖ ≤ 2 * R * M₀ := norm_transform_le_L1 hR hgc hM₀ hsupp ξ
        _ ≤ 8 * R * M₀ * (1 + |ξ|)⁻¹ ^ 2 := by
          have := window_ge_quarter_of_le_one hξ
          nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hR) hM₀']
        _ ≤ (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hw; linarith
    · have hξ1 : 1 ≤ |ξ| := le_of_not_ge hξ
      calc ‖∫ x : ℝ, Complex.exp (cst ξ * x) * g x‖
          ≤ (2 * R * M₂ + J) / Real.pi ^ 2 * (1 + |ξ|)⁻¹ ^ 2 :=
            norm_transform_le_of_one_le hR hgm hgp hm hp hsupp hM₂m hM₂p hJ hξ1
        _ ≤ (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hw; linarith
