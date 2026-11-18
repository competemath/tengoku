import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold ComplexConjugate
open UpperHalfPlane Complex Metric

namespace T2bA9

noncomputable def cay (c : ℂ) (u : ℂ) : ℂ := (c - conj c * u) / (1 - u)

noncomputable def uOf (c p : ℂ) : ℂ := (p - c) / (p - conj c)

/--
@isnad1 id=eq.0h1v.s3.2244a845818c from=translated src=- shape=1fa26838 vocab=cba8c70c
-/
theorem cay_zero (c : ℂ) : cay c 0 = c := by simp [cay]

/--
@isnad1 id=ne.1h1v.s5.66695d3f34f3 from=translated src=- shape=e0aee735 vocab=0fcc4b44
-/
theorem one_sub_ne_zero {u : ℂ} (hu : ‖u‖ < 1) : (1 : ℂ) - u ≠ 0 := by
  intro h
  have : u = 1 := by linear_combination -h
  simp [this] at hu

/--
@isnad1 id=ne.2h2v.s6.75e15a81c7a9 from=translated src=- shape=bf42ef9d vocab=b953ecf7
-/
theorem sub_conj_ne_zero {c p : ℂ} (hc : 0 < c.im) (hp : 0 < p.im) : p - conj c ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/--
@isnad1 id=eq.1h2v.s6.fb7064ed7691 from=translated src=- shape=f4725752 vocab=4e3f2626
-/
theorem im_cay_mul (c u : ℂ) (hu : ‖u‖ < 1) :
    (cay c u).im * ‖1 - u‖ ^ 2 = c.im * (1 - ‖u‖ ^ 2) := by
  have h1 : (1 : ℂ) - u ≠ 0 := one_sub_ne_zero hu
  have key : cay c u * (1 - u) = c - conj c * u := by
    unfold cay; field_simp

  have h2 : (cay c u).im * ‖1 - u‖ ^ 2 = ((c - conj c * u) * conj (1 - u)).im := by
    rw [← key, mul_assoc, Complex.mul_conj, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
    ring
  rw [h2, Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/--
@isnad1 id=lt.2h2v.s5.7382ebeb16f7 from=translated src=- shape=1e3b2d24 vocab=03bb15aa
-/
theorem im_cay_pos {c u : ℂ} (hc : 0 < c.im) (hu : ‖u‖ < 1) : 0 < (cay c u).im := by
  have h := im_cay_mul c u hu
  have h1 : 0 < ‖1 - u‖ ^ 2 := by
    have := one_sub_ne_zero hu
    positivity
  have h2 : 0 < c.im * (1 - ‖u‖ ^ 2) := by
    apply mul_pos hc
    nlinarith [norm_nonneg u]
  by_contra hneg
  push Not at hneg
  have : (cay c u).im * ‖1 - u‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg h1.le
  linarith

/--
@isnad1 id=le.3h3v.s6.93c0e56692dd from=translated src=- shape=db633277 vocab=74da7c94
-/
theorem im_cay_ge {c u : ℂ} (hc : 0 < c.im) {R : ℝ} (hR : R < 1) (hu : ‖u‖ ≤ R) :
    c.im * ((1 - R ^ 2) / 4) ≤ (cay c u).im := by
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu hR
  have h := im_cay_mul c u hu1
  have hden : ‖1 - u‖ ^ 2 ≤ 4 := by
    have : ‖1 - u‖ ≤ 2 := by
      calc ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one]; linarith
        _ = 2 := by norm_num
    nlinarith [norm_nonneg (1 - u)]
  have hdenpos : 0 < ‖1 - u‖ ^ 2 := by have := one_sub_ne_zero hu1; positivity
  have hnum : 1 - R ^ 2 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  have hpos : 0 < (cay c u).im := im_cay_pos hc hu1

  have : c.im * (1 - R ^ 2) ≤ (cay c u).im * 4 := by
    calc c.im * (1 - R ^ 2) ≤ c.im * (1 - ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hnum hc.le
      _ = (cay c u).im * ‖1 - u‖ ^ 2 := h.symm
      _ ≤ (cay c u).im * 4 := mul_le_mul_of_nonneg_left hden hpos.le
  linarith

/--
@isnad1 id=eq.2h2v.s5.8343d52d3e4f from=translated src=- shape=763cfb6e vocab=92801df6
-/
theorem cay_uOf {c p : ℂ} (hc : 0 < c.im) (hp : 0 < p.im) : cay c (uOf c p) = p := by
  have h1 := sub_conj_ne_zero hc hp
  have h2 : (1 : ℂ) - uOf c p ≠ 0 := by
    unfold uOf
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq h1]
    intro h; have := congrArg Complex.im h; simp at this; linarith
  unfold cay
  rw [div_eq_iff h2]
  unfold uOf
  field_simp
  ring

/--
@isnad1 id=lt.2h2v.s5.0434959991fd from=translated src=- shape=5969a5a0 vocab=2785265e
-/
theorem norm_uOf_lt_one {c p : ℂ} (hc : 0 < c.im) (hp : 0 < p.im) : ‖uOf c p‖ < 1 := by
  unfold uOf
  have h1 := sub_conj_ne_zero hc hp
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h1)]
  have : ‖p - c‖ ^ 2 < ‖p - conj c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

/--
@isnad1 id=hasderiv.1h2v.s7.df143cd8045f from=translated src=- shape=6d4e75fb vocab=e248c97f
-/
theorem hasDerivAt_cay (c : ℂ) {u : ℂ} (hu : (1 : ℂ) - u ≠ 0) :
    HasDerivAt (cay c) ((c - conj c) / (1 - u) ^ 2) u := by
  unfold cay
  have hn : HasDerivAt (fun u : ℂ => c - conj c * u) (-conj c) u := by
    simpa using ((hasDerivAt_id u).const_mul (conj c)).const_sub c
  have hd : HasDerivAt (fun u : ℂ => (1 : ℂ) - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (1 : ℂ)
  have := hn.div hd hu
  convert this using 1
  · rfl
  · rfl
  · rfl
  ring

/--
@isnad1 id=differen.1h2v.s6.c274a53d7c42 from=translated src=- shape=747b1508 vocab=023b6df4
-/
theorem differentiableAt_cay (c : ℂ) {u : ℂ} (hu : (1 : ℂ) - u ≠ 0) : DifferentiableAt ℂ (cay c) u :=
  (hasDerivAt_cay c hu).differentiableAt

/--
@isnad1 id=analytic.1h2v.s5.789306baba24 from=translated src=- shape=747b1508 vocab=f351e008
-/
theorem analyticAt_cay (c : ℂ) {u : ℂ} (hu : (1 : ℂ) - u ≠ 0) : AnalyticAt ℂ (cay c) u := by
  apply DifferentiableOn.analyticAt (s := {u : ℂ | (1 : ℂ) - u ≠ 0})
  · intro v hv; exact (differentiableAt_cay c hv).differentiableWithinAt
  · have hopen : IsOpen {u : ℂ | (1 : ℂ) - u ≠ 0} := isOpen_ne_fun (continuous_const.sub continuous_id) continuous_const
    exact hopen.mem_nhds hu

/--
@isnad1 id=ne.2h2v.s6.100c1fcca6a7 from=translated src=- shape=deb8d08c vocab=f0e94345
-/
theorem deriv_cay_ne_zero {c u : ℂ} (hc : 0 < c.im) (hu : (1 : ℂ) - u ≠ 0) : deriv (cay c) u ≠ 0 := by
  rw [(hasDerivAt_cay c hu).deriv]
  apply div_ne_zero _ (pow_ne_zero 2 hu)
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

end T2bA9

namespace T2bA9

open MeromorphicOn in
/--
@isnad1 id=le.8h5v.s7.96bdaa498fc4 from=translated src=- shape=40fdb455 vocab=b6cde91b
-/
theorem natOrder_le_of_bound {F : ℂ → ℂ} {r R B : ℝ} (hr : 0 < r) (hrR : r < R)
    (hF : AnalyticOnNhd ℂ F (closedBall 0 R)) (hF0 : F 0 ≠ 0) (hB : 1 ≤ B)
    (hbd : ∀ u ∈ sphere (0 : ℂ) R, ‖F u‖ ≤ B * ‖F 0‖) {u₁ : ℂ} (hu₁ : ‖u₁‖ ≤ r)
    (htop : analyticOrderAt F u₁ ≠ ⊤) :
    (analyticOrderNatAt F u₁ : ℝ) ≤ Real.log B / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR

  set G : ℂ → ℂ := fun u => (F 0)⁻¹ * F u with hG
  have hGan : AnalyticOnNhd ℂ G (closedBall 0 |R|) := by
    rw [abs_of_pos hR]
    intro u hu
    exact analyticAt_const.mul (hF u hu)
  have hG0 : G 0 = 1 := by simp [hG, hF0]
  have hG0' : G 0 ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hGbd : ∀ u ∈ sphere (0 : ℂ) |R|, ‖G u‖ ≤ B := by
    intro u hu
    rw [abs_of_pos hR] at hu
    have := hbd u hu
    simp only [hG, norm_mul, norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hF0)]
    linarith
  have hJ := AnalyticOnNhd.sum_divisor_le (c := 0) (f := G) (by rwa [abs_of_pos hr])
    (by rwa [abs_of_pos hr, abs_of_pos hR]) hB hGan hG0' hGbd
  rw [hG0, norm_one, div_one] at hJ

  have hu₁mem : u₁ ∈ closedBall (0 : ℂ) |r| := by
    rw [abs_of_pos hr, mem_closedBall, dist_zero_right]; exact hu₁
  have hGr : AnalyticOnNhd ℂ G (closedBall 0 |r|) :=
    hGan.mono (closedBall_subset_closedBall (by rw [abs_of_pos hr, abs_of_pos hR]; exact hrR.le))
  have hnn : ∀ u, 0 ≤ divisor G (closedBall (0 : ℂ) |r|) u := fun u => hGr.divisor_nonneg u
  have hsingle : (divisor G (closedBall (0 : ℂ) |r|) u₁ : ℤ) ≤ ∑ᶠ u, divisor G (closedBall (0 : ℂ) |r|) u := by
    have hfin := (divisor G (closedBall (0 : ℂ) |r|)).finiteSupport (isCompact_closedBall 0 |r|)
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
    by_cases hmem : u₁ ∈ hfin.toFinset
    · exact Finset.single_le_sum (fun u _ => hnn u) hmem
    · have : divisor G (closedBall (0 : ℂ) |r|) u₁ = 0 := by
        simpa [Function.mem_support] using hmem
      rw [this]
      exact Finset.sum_nonneg fun u _ => hnn u

  have hordG : analyticOrderAt G u₁ = analyticOrderAt F u₁ := by
    have h1 : AnalyticAt ℂ (fun _ : ℂ => (F 0)⁻¹) u₁ := analyticAt_const
    have h2 : AnalyticAt ℂ F u₁ := hF u₁ (by rw [mem_closedBall, dist_zero_right]; linarith)
    have h0 : analyticOrderAt (fun _ : ℂ => (F 0)⁻¹) u₁ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hF0))
    show analyticOrderAt ((fun _ : ℂ => (F 0)⁻¹) * F) u₁ = analyticOrderAt F u₁
    rw [analyticOrderAt_mul h1 h2, h0, zero_add]
  have hterm : (divisor G (closedBall (0 : ℂ) |r|) u₁ : ℤ) = analyticOrderNatAt F u₁ := by
    rw [hGr.divisor_apply hu₁mem, hordG, ← Nat.cast_analyticOrderNatAt htop]
    rfl
  have : ((analyticOrderNatAt F u₁ : ℤ) : ℝ) ≤ ((∑ᶠ u, divisor G (closedBall (0 : ℂ) |r|) u : ℤ) : ℝ) := by
    exact_mod_cast hterm ▸ hsingle
  calc (analyticOrderNatAt F u₁ : ℝ) = ((analyticOrderNatAt F u₁ : ℤ) : ℝ) := by norm_cast
    _ ≤ _ := this
    _ ≤ _ := hJ

end T2bA9

namespace T2bA9

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ}

noncomputable def mgauge (f : ModularForm Γ k) (τ : ℍ) : ℝ := ‖f τ‖ ^ 2 * (τ.im) ^ k

/--
@isnad1 id=eq.1h5v.s9.1dea3988f234 from=translated src=- shape=ec2b4dd0 vocab=f73f3b84
-/
theorem mgauge_smul (f : ModularForm Γ k) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ) (τ : ℍ) :
    mgauge f (γ • τ) = mgauge f τ := by
  unfold mgauge
  rw [SlashInvariantForm.slash_action_eqn'' f hγ τ, UpperHalfPlane.im_smul_eq_div_normSq,
    Complex.normSq_eq_norm_sq, norm_mul, norm_zpow]
  have hdet : |γ.det.val| = 1 := by rw [Subgroup.HasDetOne.det_eq hγ]; simp
  rw [hdet, one_mul]
  have hd : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  have hX : ‖denom γ τ‖ ^ k ≠ 0 := zpow_ne_zero k hd
  rw [div_zpow, show (‖denom γ τ‖ ^ 2) ^ k = (‖denom γ τ‖ ^ k) ^ 2 by
    rw [← zpow_natCast (‖denom γ τ‖ ^ k) 2, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]]
  field_simp

/--
@isnad1 id=continuo.0h3v.s6.5d76c34a3278 from=translated src=- shape=37140793 vocab=fd9f9dbd
-/
theorem continuous_mgauge (f : ModularForm Γ k) : Continuous (mgauge f) := by
  unfold mgauge
  refine ((continuous_norm.comp f.holo'.continuous).pow 2).mul ?_
  exact Continuous.zpow₀ UpperHalfPlane.continuous_im k fun τ => Or.inl τ.im_pos.ne'

/--
@isnad1 id=ex.2h4v.s9.5b117394acbf from=translated src=- shape=3feb139b vocab=c661240a
-/
theorem exists_max_mem (K : Set ℍ) (hK : IsCompact K) (hcov : ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (f : ModularForm Γ k) : ∃ c ∈ K, ∀ τ : ℍ, mgauge f τ ≤ mgauge f c := by
  have hne : K.Nonempty := by
    obtain ⟨γ, -, h⟩ := hcov UpperHalfPlane.I
    exact ⟨_, h⟩
  obtain ⟨c, hcK, hmax⟩ := hK.exists_isMaxOn hne (continuous_mgauge f).continuousOn
  refine ⟨c, hcK, fun τ => ?_⟩
  obtain ⟨γ, hγ, hγτ⟩ := hcov τ
  rw [← mgauge_smul f hγ τ]
  exact hmax hγτ

def U : Set ℂ := {z : ℂ | 0 < z.im}

omit [Γ.HasDetOne] in
/--
@isnad1 id=isopen.0h0v.s4.b570c4866640 from=translated src=- shape=25b03439 vocab=69d2d522
-/
theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

omit [Γ.HasDetOne] in
/--
@isnad1 id=differen.0h3v.s7.f52bba05d5c8 from=translated src=- shape=24f8ebbf vocab=c0de0384
-/
theorem differentiableOn_comp_ofComplex (f : ModularForm Γ k) :
    DifferentiableOn ℂ (fun z : ℂ => f (ofComplex z)) U := by
  intro z hz
  have h := (UpperHalfPlane.mdifferentiableAt_iff (f := f) (τ := ⟨z, hz⟩)).mp (f.holo' ⟨z, hz⟩)
  exact h.differentiableWithinAt

omit [Γ.HasDetOne] in
/--
@isnad1 id=analytic.1h4v.s7.510f6790aa4b from=translated src=- shape=e630e3a4 vocab=2db23cf3
-/
theorem analyticAt_comp_ofComplex (f : ModularForm Γ k) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (fun z : ℂ => f (ofComplex z)) z :=
  (differentiableOn_comp_ofComplex f).analyticAt (isOpen_U.mem_nhds hz)

/--
@isnad1 id=eq.1h5v.s9.d0ef44817d71 from=translated src=- shape=b5cb942f vocab=37d9bf96
-/
theorem analyticOrderAt_smul (f : ModularForm Γ k) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ) (τ : ℍ) :
    analyticOrderAt (fun z : ℂ => f (ofComplex z)) ((γ • τ : ℍ) : ℂ) =
      analyticOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) := by
  have hdet : 0 < γ.det.val := by rw [Subgroup.HasDetOne.det_eq hγ]; exact one_pos

  let m : ℂ → ℂ := fun z => num γ z / denom γ z
  have hmτ : m τ = ((γ • τ : ℍ) : ℂ) := (coe_smul_of_det_pos hdet τ).symm
  have hden : ∀ z : ℂ, 0 < z.im → denom γ z ≠ 0 := fun z hz => denom_ne_zero_of_im γ hz.ne'
  have hm_an : AnalyticAt ℂ m τ := by
    apply DifferentiableOn.analyticAt (s := U) _ (isOpen_U.mem_nhds τ.im_pos)
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold m num denom
    exact ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)).div
      ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)) (hden z hz)
  have hm_deriv : deriv m τ ≠ 0 := by
    have hd : HasDerivAt m ((γ 0 0 * denom γ τ - num γ τ * γ 1 0) / denom γ τ ^ 2) τ := by
      unfold m
      have h1 : HasDerivAt (fun z : ℂ => num γ z) (γ 0 0) τ := by
        unfold num; simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 0 0 : ℝ) : ℂ)).add_const ((γ 0 1 : ℝ) : ℂ)
      have h2 : HasDerivAt (fun z : ℂ => denom γ z) (γ 1 0) τ := by
        unfold denom; simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((γ 1 0 : ℝ) : ℂ)).add_const ((γ 1 1 : ℝ) : ℂ)
      exact h1.div h2 (hden τ τ.im_pos)
    rw [hd.deriv]
    apply div_ne_zero _ (pow_ne_zero 2 (hden τ τ.im_pos))

    have : (γ 0 0 : ℂ) * denom γ τ - num γ τ * γ 1 0 = (γ.det.val : ℂ) := by
      simp only [denom, num, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      push_cast; ring
    rw [this]
    exact_mod_cast hdet.ne'

  have hEq : (fun z : ℂ => f (ofComplex (m z))) =ᶠ[𝓝 (τ : ℂ)]
      fun z : ℂ => denom γ z ^ k * f (ofComplex z) := by
    filter_upwards [isOpen_U.mem_nhds τ.im_pos] with z hz
    have hz' : ofComplex z = ⟨z, hz⟩ := by
      rw [← ofComplex_apply ⟨z, hz⟩]
    have : m z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := (coe_smul_of_det_pos hdet ⟨z, hz⟩).symm
    rw [this, ofComplex_apply, hz', SlashInvariantForm.slash_action_eqn'' f hγ ⟨z, hz⟩]
  have h1 : analyticOrderAt ((fun z : ℂ => f (ofComplex z)) ∘ m) τ =
      analyticOrderAt (fun z : ℂ => f (ofComplex z)) (m τ) :=
    analyticOrderAt_comp_of_deriv_ne_zero hm_an hm_deriv
  rw [← hmτ, ← h1, show ((fun z : ℂ => f (ofComplex z)) ∘ m) = fun z => f (ofComplex (m z)) from rfl,
    analyticOrderAt_congr hEq]
  have hd_an : AnalyticAt ℂ (fun z : ℂ => denom γ z ^ k) τ := by
    apply DifferentiableOn.analyticAt (s := U) _ (isOpen_U.mem_nhds τ.im_pos)
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold denom
    exact (((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)).zpow
      (Or.inl (hden z hz))
  have hd0 : analyticOrderAt (fun z : ℂ => denom γ z ^ k) τ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (zpow_ne_zero k (hden τ τ.im_pos)))
  rw [show (fun z : ℂ => denom γ z ^ k * f (ofComplex z)) =
      (fun z : ℂ => denom γ z ^ k) * (fun z : ℂ => f (ofComplex z)) from rfl,
    analyticOrderAt_mul hd_an (analyticAt_comp_ofComplex f τ.im_pos), hd0, zero_add]

end T2bA9

namespace T2bA9

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ}

omit [Γ.HasDetOne] in
/--
@isnad1 id=analytic.1h5v.s7.07ed8bcd3614 from=translated src=- shape=89664823 vocab=973c3a99
-/
theorem analyticAt_fibre (f : ModularForm Γ k) (c : ℍ) {u : ℂ} (hu : ‖u‖ < 1) :
    AnalyticAt ℂ (fun u : ℂ => f (ofComplex (cay c u))) u := by
  have h1 : (1 : ℂ) - u ≠ 0 := one_sub_ne_zero hu
  have h2 : 0 < (cay c u).im := im_cay_pos c.im_pos hu
  exact (analyticAt_comp_ofComplex f h2).comp (analyticAt_cay c h1)

/--
@isnad1 id=ne.2h4v.s7.fb0b6747b339 from=translated src=- shape=c4ab5642 vocab=40db22f0
-/
theorem apply_ne_zero_of_max (f : ModularForm Γ k) (hf : (f : ℍ → ℂ) ≠ 0) {c : ℍ}
    (hmax : ∀ τ : ℍ, mgauge f τ ≤ mgauge f c) : f c ≠ 0 := by
  intro h0
  apply hf
  funext τ
  have h := hmax τ
  have hM : mgauge f c = 0 := by unfold mgauge; rw [h0, norm_zero]; simp
  rw [hM] at h
  unfold mgauge at h
  have hy : 0 < (τ.im : ℝ) ^ k := zpow_pos τ.im_pos k
  have h2 : ‖f τ‖ ^ 2 ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have := mul_pos hneg hy
    linarith
  have : ‖f τ‖ = 0 := by nlinarith [norm_nonneg (f τ)]
  simpa using this

/--
@isnad1 id=le.5h7v.s8.c711ea9185ff from=translated src=- shape=896daf1a vocab=36831b25
-/
theorem fibre_bound (f : ModularForm Γ k) (n : ℕ) (hk : k = n) {c : ℍ}
    (hmax : ∀ τ : ℍ, mgauge f τ ≤ mgauge f c) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    {u : ℂ} (hu : ‖u‖ ≤ R) :
    ‖f (ofComplex (cay c u))‖ ≤ (((1 - R ^ 2) / 4)⁻¹) ^ n * ‖f c‖ := by
  set δ : ℝ := (1 - R ^ 2) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; nlinarith
  have hδle : δ ≤ 1 := by rw [hδ]; nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu hR1
  have him : 0 < (cay c u).im := im_cay_pos c.im_pos hu1
  have hτeq : ofComplex (cay c u) = ⟨cay c u, him⟩ := by rw [← ofComplex_apply ⟨cay c u, him⟩]
  rw [hτeq]
  set τ : ℍ := ⟨cay c u, him⟩ with hτ
  have hyge : c.im * δ ≤ τ.im := im_cay_ge c.im_pos hR1 hu
  have hycpos : 0 < c.im := c.im_pos

  have hg : ‖f τ‖ ^ 2 * τ.im ^ n ≤ ‖f c‖ ^ 2 * c.im ^ n := by
    have := hmax τ
    unfold mgauge at this
    have e1 : (τ.im : ℝ) ^ k = τ.im ^ n := by rw [hk, zpow_natCast]
    have e2 : (c.im : ℝ) ^ k = c.im ^ n := by rw [hk, zpow_natCast]
    rwa [e1, e2] at this
  have hpow : (c.im * δ) ^ n ≤ τ.im ^ n := pow_le_pow_left₀ (by positivity) hyge n
  set B : ℝ := (δ⁻¹) ^ n with hB
  have hB1 : 1 ≤ B := one_le_pow₀ (one_le_inv_iff₀.mpr ⟨hδpos, hδle⟩)
  have hBδ : B * δ ^ n = 1 := by rw [hB, inv_pow, inv_mul_cancel₀ (pow_ne_zero n hδpos.ne')]

  have h1 : ‖f τ‖ ^ 2 * (c.im ^ n * δ ^ n) ≤ ‖f c‖ ^ 2 * c.im ^ n := by
    rw [← mul_pow]
    exact (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)).trans hg
  have hcn : 0 < c.im ^ n := pow_pos hycpos n
  have h2 : ‖f τ‖ ^ 2 * δ ^ n ≤ ‖f c‖ ^ 2 := by
    have : (‖f τ‖ ^ 2 * δ ^ n) * c.im ^ n ≤ ‖f c‖ ^ 2 * c.im ^ n := by nlinarith
    exact le_of_mul_le_mul_right this hcn
  have h3 : ‖f τ‖ ^ 2 ≤ (B * ‖f c‖) ^ 2 := by
    have h4 : ‖f τ‖ ^ 2 ≤ B * ‖f c‖ ^ 2 := by
      have : B * (‖f τ‖ ^ 2 * δ ^ n) ≤ B * ‖f c‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
      calc ‖f τ‖ ^ 2 = B * (‖f τ‖ ^ 2 * δ ^ n) := by
            rw [mul_comm B, mul_assoc, mul_comm (δ ^ n), hBδ, mul_one]
        _ ≤ B * ‖f c‖ ^ 2 := this
    calc ‖f τ‖ ^ 2 ≤ B * ‖f c‖ ^ 2 := h4
      _ ≤ B ^ 2 * ‖f c‖ ^ 2 := by nlinarith [sq_nonneg ‖f c‖]
      _ = (B * ‖f c‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg (f τ)) (by positivity : 0 ≤ B * ‖f c‖) two_ne_zero).mp h3

end T2bA9

namespace T2bA9

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ}

/--
@isnad1 id=ex.2h2v.s9.4248d1f0a5aa from=translated src=- shape=9dccc0ef vocab=d53612b7
-/
theorem exists_order_bound (K : Set ℍ) (hK : IsCompact K) (hcov : ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    ∃ C : ℕ, ∀ (k : ℤ) (n : ℕ), k = n → ∀ f : ModularForm Γ k, (f : ℍ → ℂ) ≠ 0 → ∀ τ : ℍ,
      analyticOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) ≤ (C * n : ℕ) := by
  classical
  have hne : K.Nonempty := by
    obtain ⟨γ, -, h⟩ := hcov UpperHalfPlane.I
    exact ⟨_, h⟩

  let ρ : ℍ × ℍ → ℝ := fun q => ‖uOf (q.1 : ℂ) (q.2 : ℂ)‖
  have hρc : Continuous ρ := by
    apply Continuous.norm
    apply Continuous.div
    · exact (continuous_coe.comp continuous_snd).sub (continuous_coe.comp continuous_fst)
    · exact (continuous_coe.comp continuous_snd).sub
        (Complex.continuous_conj.comp (continuous_coe.comp continuous_fst))
    · intro q
      exact sub_conj_ne_zero q.1.im_pos q.2.im_pos
  obtain ⟨q₀, hq₀, hqmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne) hρc.continuousOn
  set r₀ : ℝ := ρ q₀ with hr₀
  have hr₀1 : r₀ < 1 := norm_uOf_lt_one q₀.1.im_pos q₀.2.im_pos
  have hr₀0 : 0 ≤ r₀ := norm_nonneg _
  have hρle : ∀ c ∈ K, ∀ p ∈ K, ‖uOf (c : ℂ) (p : ℂ)‖ ≤ r₀ := fun c hc p hp => by
    have := hqmax (Set.mk_mem_prod hc hp)
    simpa [ρ] using this
  set R₀ : ℝ := (1 + r₀) / 2 with hR₀
  have hR₀1 : R₀ < 1 := by rw [hR₀]; linarith
  have hR₀0 : 0 < R₀ := by rw [hR₀]; linarith
  have hr₀R : r₀ < R₀ := by rw [hR₀]; linarith
  set r : ℝ := max r₀ (R₀ / 2) with hr
  have hr0 : 0 < r := lt_max_of_lt_right (by linarith)
  have hrR : r < R₀ := max_lt hr₀R (by linarith)
  have hr₀r : r₀ ≤ r := le_max_left _ _
  set δ : ℝ := (1 - R₀ ^ 2) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; nlinarith
  have hδle : δ ≤ 1 := by rw [hδ]; nlinarith
  set L : ℝ := Real.log δ⁻¹ / Real.log (R₀ / r) with hL
  have hlogRr : 0 < Real.log (R₀ / r) := Real.log_pos ((one_lt_div hr0).mpr hrR)
  have hL0 : 0 ≤ L := div_nonneg (Real.log_nonneg ((one_le_inv_iff₀.mpr ⟨hδpos, hδle⟩))) hlogRr.le
  refine ⟨⌈L⌉₊, fun k n hk f hf τ₁ => ?_⟩

  obtain ⟨c, hcK, hmax⟩ := exists_max_mem K hK hcov f
  have hfc : f c ≠ 0 := apply_ne_zero_of_max f hf hmax
  obtain ⟨γ₁, hγ₁, hpK⟩ := hcov τ₁
  set p : ℍ := γ₁ • τ₁ with hp
  set u₁ : ℂ := uOf (c : ℂ) (p : ℂ) with hu₁
  have hu₁r : ‖u₁‖ ≤ r := (hρle c hcK p hpK).trans hr₀r
  have hu₁1 : ‖u₁‖ < 1 := lt_of_le_of_lt hu₁r (hrR.trans hR₀1)

  set F : ℂ → ℂ := fun u => f (ofComplex (cay c u)) with hF
  have hFan : AnalyticOnNhd ℂ F (closedBall 0 R₀) := by
    intro u hu
    rw [mem_closedBall, dist_zero_right] at hu
    exact analyticAt_fibre f c (lt_of_le_of_lt hu hR₀1)
  have hFball : AnalyticOnNhd ℂ F (ball 0 1) := by
    intro u hu
    rw [mem_ball, dist_zero_right] at hu
    exact analyticAt_fibre f c hu
  have hF0 : F 0 = f c := by
    show f (ofComplex (cay c 0)) = f c
    rw [cay_zero, ofComplex_apply]
  have hF0' : F 0 ≠ 0 := by rw [hF0]; exact hfc
  set B : ℝ := (δ⁻¹) ^ n with hB
  have hB1 : 1 ≤ B := one_le_pow₀ (one_le_inv_iff₀.mpr ⟨hδpos, hδle⟩)
  have hbd : ∀ u ∈ sphere (0 : ℂ) R₀, ‖F u‖ ≤ B * ‖F 0‖ := by
    intro u hu
    rw [mem_sphere, dist_zero_right] at hu
    rw [hF0]
    have := fibre_bound f n hk hmax hR₀0.le hR₀1 (le_of_eq hu)
    rw [← hδ] at this
    exact this
  have htop : analyticOrderAt F u₁ ≠ ⊤ := by
    have h0 : analyticOrderAt F 0 ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hF0')]; exact ENat.zero_ne_top
    exact hFball.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 1).isPreconnected
      (mem_ball_self one_pos) (by rw [mem_ball, dist_zero_right]; exact hu₁1) h0

  have hJ := natOrder_le_of_bound hr0 hrR hFan hF0' hB1 hbd hu₁r htop
  have hlogB : Real.log B = n * Real.log δ⁻¹ := by rw [hB, Real.log_pow]
  have hnat : analyticOrderNatAt F u₁ ≤ ⌈L⌉₊ * n := by
    have h1 : (analyticOrderNatAt F u₁ : ℝ) ≤ n * L := by
      rw [hlogB] at hJ
      rw [hL, ← mul_div_assoc]
      exact hJ
    have h2 : (n : ℝ) * L ≤ n * ⌈L⌉₊ := mul_le_mul_of_nonneg_left (Nat.le_ceil L) (Nat.cast_nonneg n)
    have h3 : (analyticOrderNatAt F u₁ : ℝ) ≤ ((⌈L⌉₊ * n : ℕ) : ℝ) := by
      rw [Nat.cast_mul, mul_comm]; exact h1.trans h2
    exact_mod_cast h3

  have h1u : (1 : ℂ) - u₁ ≠ 0 := one_sub_ne_zero hu₁1
  have hcomp' : analyticOrderAt ((fun z : ℂ => f (ofComplex z)) ∘ cay (c : ℂ)) u₁ =
      analyticOrderAt (fun z : ℂ => f (ofComplex z)) (cay c u₁) :=
    analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_cay c h1u) (deriv_cay_ne_zero c.im_pos h1u)
  have hFdef : F = ((fun z : ℂ => f (ofComplex z)) ∘ cay (c : ℂ)) := rfl
  have hcomp : analyticOrderAt F u₁ = analyticOrderAt (fun z : ℂ => f (ofComplex z)) (cay c u₁) := by
    rw [hFdef]; exact hcomp'
  have hcayu : cay c u₁ = (p : ℂ) := cay_uOf c.im_pos p.im_pos
  have hsm : analyticOrderAt (fun z : ℂ => f (ofComplex z)) (p : ℂ) =
      analyticOrderAt (fun z : ℂ => f (ofComplex z)) (τ₁ : ℂ) := analyticOrderAt_smul f hγ₁ τ₁
  rw [← hsm, ← hcayu, ← hcomp, ← Nat.cast_analyticOrderNatAt htop]
  exact_mod_cast hnat

/--
@isnad1 id=and.1h3v.s7.7abfa1d21d87 from=translated src=- shape=4d62171c vocab=de13be67
-/
theorem finite_and_finrank_le_of_orderBound (k : ℤ) (B : ℕ)
    (h : ∀ f : ModularForm Γ k, (f : ℍ → ℂ) ≠ 0 →
      analyticOrderAt (fun z : ℂ => f (ofComplex z)) (UpperHalfPlane.I : ℂ) ≤ B) :
    FiniteDimensional ℂ (ModularForm Γ k) ∧ Module.finrank ℂ (ModularForm Γ k) ≤ B + 1 := by
  have han : ∀ f : ModularForm Γ k, AnalyticAt ℂ (fun z : ℂ => f (ofComplex z)) (UpperHalfPlane.I : ℂ) :=
    fun f => analyticAt_comp_ofComplex f UpperHalfPlane.I.im_pos
  let J : ModularForm Γ k →ₗ[ℂ] (Fin (B + 1) → ℂ) :=
    { toFun := fun f i => iteratedDeriv i (fun z : ℂ => f (ofComplex z)) (UpperHalfPlane.I : ℂ)
      map_add' := fun f g => by
        funext i
        have hfg : (fun z : ℂ => (f + g) (ofComplex z)) =
            (fun z : ℂ => f (ofComplex z)) + fun z : ℂ => g (ofComplex z) := by
          funext z; simp [add_apply]
        show iteratedDeriv i (fun z : ℂ => (f + g) (ofComplex z)) _ = iteratedDeriv i _ _ + iteratedDeriv i _ _
        rw [hfg]
        exact iteratedDeriv_add ((han f).contDiffAt.of_le le_top) ((han g).contDiffAt.of_le le_top)
      map_smul' := fun a f => by
        funext i
        have hfg : (fun z : ℂ => (a • f) (ofComplex z)) = a • fun z : ℂ => f (ofComplex z) := by
          funext z; simp
        show iteratedDeriv i (fun z : ℂ => (a • f) (ofComplex z)) _ = a • iteratedDeriv i _ _
        rw [hfg]
        exact iteratedDeriv_const_smul ((han f).contDiffAt.of_le le_top) a }
  have hinj : Function.Injective J := by
    intro f g hfg
    rw [← sub_eq_zero]
    by_contra hne
    have hne' : ((f - g : ModularForm Γ k) : ℍ → ℂ) ≠ 0 := by
      intro h0; apply hne; exact DFunLike.coe_injective (by simpa using h0)
    have hB := h (f - g) hne'
    have hJ0 : J (f - g) = 0 := by rw [map_sub, hfg, sub_self]
    have hzero : ∀ i < B + 1, iteratedDeriv i (fun z : ℂ => (f - g) (ofComplex z)) (UpperHalfPlane.I : ℂ) = 0 := by
      intro i hi
      have := congrFun hJ0 ⟨i, hi⟩
      exact this
    have hle : ((B + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z : ℂ => (f - g) (ofComplex z)) (UpperHalfPlane.I : ℂ) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han (f - g))).mpr hzero
    have : ((B + 1 : ℕ) : ℕ∞) ≤ (B : ℕ) := hle.trans hB
    have : B + 1 ≤ B := by exact_mod_cast this
    omega
  haveI : FiniteDimensional ℂ (ModularForm Γ k) := FiniteDimensional.of_injective J hinj
  refine ⟨this, ?_⟩
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at this

end T2bA9

open T2bA9 in
/--
@isnad1 id=ex.1h1v.s10.082ea04a4641 from=translated src=- shape=ec1c2f65 vocab=694966d3
-/
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    ∃ C : ℕ, ∀ k : ℤ, 0 ≤ k →
      (∀ f : ModularForm Γ k, (f : ℍ → ℂ) ≠ 0 → ∀ τ : ℍ,
        meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) ≤ (((C : ℤ) * k : ℤ) : WithTop ℤ)) ∧
      FiniteDimensional ℂ (ModularForm Γ k) ∧
      Module.finrank ℂ (ModularForm Γ k) ≤ C * k.toNat + 1 := by
  obtain ⟨K, hK, hcov⟩ := hcpt
  obtain ⟨C, hC⟩ := exists_order_bound (Γ := Γ) K hK hcov
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
  have hkn : k.toNat = n := by omega
  refine ⟨fun f hf τ => ?_, ?_⟩
  · have h := hC k n hn f hf τ
    have han := analyticAt_comp_ofComplex f τ.im_pos
    rw [han.meromorphicOrderAt_eq]
    have htop : analyticOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hm] at h ⊢
    have hmle : m ≤ C * n := by exact_mod_cast h
    show ((m : ℤ) : WithTop ℤ) ≤ (((C : ℤ) * k : ℤ) : WithTop ℤ)
    rw [hn]
    exact_mod_cast hmle
  · have := finite_and_finrank_le_of_orderBound (Γ := Γ) k (C * n) fun f hf => hC k n hn f hf UpperHalfPlane.I
    rw [hkn]
    exact this
