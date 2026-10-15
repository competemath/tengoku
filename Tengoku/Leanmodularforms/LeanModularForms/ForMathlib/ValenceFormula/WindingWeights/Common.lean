/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Tengoku
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.SegmentFTC
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.TrigLemmas
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ValenceFormula.Boundary.Smooth

/-!
# Shared Infrastructure for Winding Weight Computations

Common helpers used across the ρ, ρ+1, and i winding weight proofs:
trigonometric identities, old-style segment selectors, the unified arc
formula, and FTC lemmas for log-derivative integrals.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/--
@isnad1 id=eq.0h1v.s3.6d36ee547da9 from=translated src=- shape=a62063d2 vocab=2b055d7f
-/
theorem fdBoundary_H_at_one_eq_rho_plus_one (H : ℝ) :
    fdBoundary_H H 1 = ellipticPointRhoPlusOne := by
  simp [fdBoundary_H, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']

/--
@isnad1 id=eq.0h1v.s3.9010f22dce43 from=translated src=- shape=a62063d2 vocab=827cedfd
-/
theorem fdBoundary_H_at_two_eq_I (H : ℝ) :
    fdBoundary_H H 2 = I := by
  simp only [fdBoundary_H, show ¬((2 : ℝ) ≤ 1) by norm_num, le_refl, ↓reduceIte]
  rw [show ((↑(Real.pi : ℝ) / 3 + (↑(2:ℝ) - 1) *
      (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I = ↑(Real.pi / 2) * I) by push_cast; ring,
    Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

/--
@isnad1 id=eq.0h1v.s3.b821226779cf from=translated src=- shape=a62063d2 vocab=d0075599
-/
theorem fdBoundary_H_at_three_eq_rho (H : ℝ) :
    fdBoundary_H H 3 = ellipticPointRho := by
  simp only [fdBoundary_H, show ¬((3 : ℝ) ≤ 1) by norm_num,
    show ¬((3 : ℝ) ≤ 2) by norm_num, le_refl, ↓reduceIte]
  rw [show ((↑(Real.pi : ℝ) / 2 + (↑(3:ℝ) - 2) *
      (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I = ↑(2 * Real.pi / 3) * I) by
    push_cast; ring,
    Complex.exp_ofReal_mul_I, cos_two_pi_div_three, sin_two_pi_div_three]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  push_cast; ring

/--
@isnad1 id=eq.1h2v.s6.18958c473db7 from=translated src=- shape=596ff9b4 vocab=d7ae0321
-/
theorem fdBoundary_H_seg1 (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t = 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  simp only [fdBoundary_H, ht, ↓reduceIte]

/--
@isnad1 id=eq.2h2v.s7.426394ba74ac from=translated src=- shape=3d3b8b84 vocab=4c136ae6
-/
theorem fdBoundary_H_seg2 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : t ≤ 2) :
    fdBoundary_H H t = exp ((↑(Real.pi : ℝ) / 3 + (↑t - 1) *
      (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I) := by
  simp only [fdBoundary_H, ht1, ht2, ↓reduceIte]

/--
@isnad1 id=eq.3h2v.s7.1c85d1e1f189 from=translated src=- shape=a5b750b2 vocab=4c136ae6
-/
theorem fdBoundary_H_seg3 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : t ≤ 3) :
    fdBoundary_H H t = exp ((↑(Real.pi : ℝ) / 2 + (↑t - 2) *
      (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I) := by
  simp only [fdBoundary_H, ht1, ht2, ht3, ↓reduceIte]

/--
@isnad1 id=eq.4h2v.s7.26783a2c101a from=translated src=- shape=e601d414 vocab=ab3422fd
-/
theorem fdBoundary_H_seg4 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : ¬(t ≤ 3)) (ht4 : t ≤ 4) :
    fdBoundary_H H t = -1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) *
      (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  simp only [fdBoundary_H, ht1, ht2, ht3, ht4, ↓reduceIte]

/--
@isnad1 id=eq.4h2v.s6.ff536d671531 from=translated src=- shape=5adbe2ab vocab=b220b7e3
-/
theorem fdBoundary_H_seg5 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : ¬(t ≤ 3)) (ht4 : ¬(t ≤ 4)) :
    fdBoundary_H H t = (↑t - 9/2) + ↑H * I := by
  simp only [fdBoundary_H, ht1, ht2, ht3, ht4, ↓reduceIte]

/--
@isnad1 id=eq.2h2v.s6.553d652a0695 from=translated src=- shape=d551ed1d vocab=4c4bbaed
-/
theorem fdBoundary_H_eq_arc {H : ℝ} {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundary_H H t = Complex.exp (↑(Real.pi * (1 + t) / 6) * I) := by
  simp only [fdBoundary_H, show ¬(t ≤ 1) by linarith, ↓reduceIte]
  by_cases h2 : t ≤ 2 <;>
    simp only [h2, ↓reduceIte, ht3.le] <;>
    congr 1 <;> push_cast <;> ring

/--
@isnad1 id=and.8h4v.s9.4f2b6e97ac13 from=translated src=- shape=233f0c07 vocab=73f84612
-/
lemma ftc_log_pieceFM {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  LogDerivFTC.ftc_log_pieceFM hab hh_cont hh_diff hh_deriv_cont hh_slit heq heq_a heq_b

/--
@isnad1 id=continuo.0h0v.s5.771c2ab1061c from=translated src=- shape=a8db63f6 vocab=5d07d02a
-/
lemma continuousOn_arg_im_nonneg :
    ContinuousOn Complex.arg {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  intro z ⟨hz_im, hz_ne⟩
  exact ContinuousWithinAt.congr
    ((continuous_re.continuousWithinAt.div continuous_norm.continuousWithinAt
      (norm_ne_zero_iff.mpr hz_ne)).arccos)
    (fun w ⟨hw_im, hw_ne⟩ => Complex.arg_of_im_nonneg_of_ne_zero hw_im hw_ne)
    (Complex.arg_of_im_nonneg_of_ne_zero hz_im hz_ne)

/--
@isnad1 id=continuo.0h0v.s5.61bb84db31fa from=translated src=- shape=adee25a8 vocab=f75b934c
-/
lemma continuousOn_clog_im_nonneg :
    ContinuousOn Complex.log {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  intro z ⟨hz_im, hz_ne⟩
  rw [show Complex.log = fun w => ↑(Real.log ‖w‖) + ↑(Complex.arg w) * I from funext fun _ => rfl]
  refine ContinuousWithinAt.add ?_ ?_
  · exact (continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz_ne)).comp
        continuous_norm.continuousAt)).continuousWithinAt
  · exact (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuousOn_arg_im_nonneg z ⟨hz_im, hz_ne⟩)).mul continuousWithinAt_const

/-- Auxiliary: transport integrability of `deriv h / h` to `deriv g / g`
when `g = h` on `Ioo a b`, returning both the AE-equality and `IntervalIntegrable g'/g`. -/
private lemma ftc_log_piece_congr_aux {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b) :
    (∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume a b := by
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume := by simp [mem_ae_iff]
  have h_congr : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    have ht_ne : t ≠ b := fun h => ht_ne_b (mem_singleton_iff.mpr h)
    rw [uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
    rw [hval, hderiv]
  refine ⟨h_congr, ?_, ?_⟩
  · exact MeasureTheory.Integrable.congr
      (show Integrable _ (volume.restrict (Ioc a b)) from hint_h.1)
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (h_congr.mono (fun t ht hm => (ht (uIoc_of_le hab ▸ hm)).symm)))
  · rw [show Ioc b a = ∅ from Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact MeasureTheory.integrableOn_empty

/--
@isnad1 id=and.10h4v.s9.a6fe0f7d0a69 from=translated src=- shape=5bf3b2eb vocab=e830903e
-/
lemma ftc_log_piece_upper {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_im_nn : ∀ t ∈ Icc a b, 0 ≤ (h t).im) (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0)
    (hh_slit_interior : ∀ t ∈ Ioo a b, h t ∈ slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hh_log_cont : ContinuousOn (fun t => Complex.log (h t)) (Icc a b) :=
    ContinuousOn.comp continuousOn_clog_im_nonneg hh_cont
      (fun t ht => ⟨hh_im_nn t ht, hh_ne t ht⟩)
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hh_ne).mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  obtain ⟨h_congr, hint_g⟩ := ftc_log_piece_congr_aux hab heq hint_h
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hh_log_cont (fun t ht => (hh_diff t ht).hasDerivAt.clog_real
      (hh_slit_interior t ht)) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (h b) - Complex.log (h a) := h_ftc
      _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]⟩

/--
@isnad1 id=and.10h4v.s9.9fd84180b896 from=translated src=- shape=5c891a64 vocab=1df0af45
-/
lemma ftc_log_piece_lower {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_im_np : ∀ t ∈ Icc a b, (h t).im ≤ 0) (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0)
    (hh_im_neg_interior : ∀ t ∈ Ioo a b, (h t).im < 0)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t =
      Complex.log (-(g b)) - Complex.log (-(g a)) := by
  have hnh_log_cont : ContinuousOn (fun t => Complex.log (-(h t))) (Icc a b) :=
    ContinuousOn.comp continuousOn_clog_im_nonneg hh_cont.neg fun t ht =>
      ⟨by simpa using hh_im_np t ht, neg_ne_zero.mpr (hh_ne t ht)⟩
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hh_ne).mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  obtain ⟨h_congr, hint_g⟩ := ftc_log_piece_congr_aux hab heq hint_h
  have hnh_slit : ∀ t ∈ Ioo a b, (-(h t)) ∈ slitPlane := fun t ht => by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inr (by simpa using ne_of_lt (hh_im_neg_interior t ht))
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hnh_log_cont (fun t ht => by
      have := (hh_diff t ht).hasDerivAt.neg.clog_real (hnh_slit t ht)
      exact (show -deriv h t / -h t = deriv h t / h t by simp only [neg_div_neg_eq]) ▸ this) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (-(h b)) - Complex.log (-(h a)) := h_ftc
      _ = Complex.log (-(g b)) - Complex.log (-(g a)) := by rw [heq_a, heq_b]⟩

/-! ### Shared derivative and trigonometric lemmas used by the i, ρ, ρ+1 proofs -/

/-- Derivative of the parametric arc `exp(i·π(1+t)/6) - s`.
@isnad1 id=hasderiv.0h2v.s7.0e0b72a154a9 from=translated src=- shape=453f628c vocab=caed9cfb
-/
lemma hasDerivAt_arc_sub_const (s : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (↑(Real.pi * (1 + t) / 6) * I) - s)
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
    ((hasDerivAt_id t).add_const (1:ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => by simp [id]; ring) |>.congr_deriv (by ring)
  have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
      ((↑(Real.pi / 6) : ℂ) * I) t :=
    (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  exact (hci.cexp.sub (hasDerivAt_const t s)).congr_deriv (by simp only [sub_zero]; ring)

/-- Closed-contour property: `fdBoundary_H H 0 - c = fdBoundary_H H 5 - c`.
@isnad1 id=eq.0h2v.s5.8fb243b8327d from=translated src=- shape=4d3e8838 vocab=d3492c3f
-/
lemma fdBoundary_H_sub_closed (H : ℝ) (c : ℂ) :
    fdBoundary_H H 0 - c = fdBoundary_H H 5 - c := by rw [fdBoundary_H_closed H]

/-- Continuity of the arc-derivative expression `(π/6)·i·exp(i·π(1+t)/6)`.
@isnad1 id=continuo.0h0v.s6.6e5c4f00b50b from=translated src=- shape=63ff3ff6 vocab=dea6844c
-/
@[fun_prop]
lemma continuous_arc_deriv :
    Continuous fun t : ℝ => (↑(Real.pi / 6) : ℂ) * I *
      Complex.exp (↑(Real.pi * (1 + t) / 6) * I) := by
  fun_prop

/-- Continuity of `deriv h` for any `h` with the canonical arc-derivative form.
@isnad1 id=continuo.1h3v.s7.325fd15dff34 from=translated src=- shape=882ce84b vocab=0d0059f6
-/
lemma continuousOn_deriv_of_arc_form {h : ℝ → ℂ}
    (hd : ∀ t : ℝ, HasDerivAt h
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I)) t)
    (a b : ℝ) : ContinuousOn (deriv h) (Icc a b) := by
  rw [show deriv h =
      fun t => ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I) from
    funext fun t => (hd t).deriv]
  exact continuous_arc_deriv.continuousOn

/-- Derivative of the final segment `t ↦ ↑(t - c) + d`, which equals `1`.
@isnad1 id=hasderiv.0h3v.s6.4b5d04d82a6e from=translated src=- shape=f184e880 vocab=ae7e7e51
-/
lemma hasDerivAt_seg5_line (c : ℝ) (d : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (↑(s - c) : ℂ) + d) 1 t :=
  (((hasDerivAt_id t).sub_const c).ofReal_comp.add (hasDerivAt_const t d)).congr_deriv
    (by simp only [Complex.ofReal_one, add_zero])

/-- Derivative of `t ↦ ↑((c - t) · k) · I`: slope `−k · I`.
@isnad1 id=hasderiv.0h3v.s6.5bcb70596697 from=translated src=- shape=561e098d vocab=f3ba1c09
-/
lemma hasDerivAt_aff_imI_neg (k : ℝ) (c : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (↑((c - s) * k) : ℂ) * I) (-(↑k : ℂ) * I) t := by
  have h1 : HasDerivAt (fun s : ℝ => (c - s) * k) (-k) t :=
    (((hasDerivAt_const t c).sub (hasDerivAt_id t)).mul_const k).congr_deriv (by ring)
  exact (h1.ofReal_comp.mul_const I).congr_deriv (by push_cast; ring)

/-- Derivative of `t ↦ ↑((t - c) · k) · I`: slope `k · I`.
@isnad1 id=hasderiv.0h3v.s6.7570202aa109 from=translated src=- shape=6a8211ab vocab=a9e4fa46
-/
lemma hasDerivAt_aff_imI_pos (k : ℝ) (c : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (↑((s - c) * k) : ℂ) * I) ((↑k : ℂ) * I) t :=
  ((((hasDerivAt_id t).sub (hasDerivAt_const t c)).mul_const k).ofReal_comp.mul_const
    I).congr_deriv (by norm_num [smul_eq_mul])

/-- Derivative of `t ↦ d + ↑(c0 + (t - c) · k) · I`: slope `k · I`.
@isnad1 id=hasderiv.0h5v.s6.d81d4e812fdc from=translated src=- shape=6a3a4de9 vocab=b85dacf6
-/
lemma hasDerivAt_aff_imI_pos_shift (d : ℂ) (k c0 : ℝ) (c : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => d + (↑(c0 + (s - c) * k) : ℂ) * I) ((↑k : ℂ) * I) t := by
  have hf : HasDerivAt (fun s : ℝ => c0 + (s - c) * k) k t :=
    ((((hasDerivAt_id t).sub_const c).mul_const k).const_add c0).congr_deriv (by ring)
  exact ((hasDerivAt_const t d).add (hf.ofReal_comp.mul_const I)).congr_deriv (by ring)

/-- The derivative of a function with constant derivative `c` is continuous.
@isnad1 id=continuo.1h4v.s7.93ca72c4826a from=translated src=- shape=04f6619a vocab=e71eb9b5
-/
lemma continuousOn_deriv_of_const {h : ℝ → ℂ} (c : ℂ) (hd : ∀ t : ℝ, HasDerivAt h c t)
    (a b : ℝ) : ContinuousOn (deriv h) (Icc a b) := by
  rw [show deriv h = fun _ => c from funext fun t => (hd t).deriv]; exact continuousOn_const

/-- Build the bundled `(g t = h t ∧ deriv g t = deriv h t)` property over an open
interval from a pointwise equality on a containing neighborhood.
@isnad1 id=and.3h6v.s7.414ba2ad5048 from=translated src=- shape=2711b2a4 vocab=53beb5cc
-/
lemma heq_deriv_of_eq_on_nhds {g h : ℝ → ℂ} {a b : ℝ}
    {U : Set ℝ} (hU : ∀ t ∈ Ioo a b, U ∈ 𝓝 t)
    (hgh : ∀ s ∈ U, g s = h s) :
    ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t := fun t ht =>
  ⟨hgh t (mem_of_mem_nhds (hU t ht)), Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (hU t ht) (fun s hs => hgh s hs))⟩

/-- Swap the form `(γ t - c)⁻¹ * deriv γ t` to `deriv (· - c) γ t / (γ t - c)`.
@isnad1 id=eq.0h2v.s7.55e88e007af2 from=translated src=- shape=2fd4f059 vocab=a4214eca
-/
lemma inv_mul_deriv_eq_logDeriv_sub (H : ℝ) (c : ℂ) :
    (fun t => (fdBoundary_H H t - c)⁻¹ * deriv (fdBoundary_H H) t) =
    (fun t => deriv (fun s => fdBoundary_H H s - c) t / (fdBoundary_H H t - c)) := by
  funext t
  have : deriv (fun s => fdBoundary_H H s - c) t = deriv (fdBoundary_H H) t :=
    deriv_sub_const (f := fdBoundary_H H) c
  rw [this, div_eq_mul_inv, mul_comm]

/-- `0 < sin(π/12)`.
@isnad1 id=lt.0h0v.s4.901e6c0967c6 from=translated src=- shape=c0f54276 vocab=3e1dccff
-/
lemma sin_pi_div_twelve_pos : 0 < Real.sin (Real.pi / 12) :=
  ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])

/-- `0 < sin(δ · π / 12)` for `0 < δ < 2`, useful in arc factor lemmas.
@isnad1 id=lt.2h1v.s5.49776641ca22 from=translated src=- shape=4ac45c49 vocab=721197ad
-/
lemma sin_delta_pi_div_twelve_pos {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 2) :
    0 < Real.sin (δ * Real.pi / 12) :=
  ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])

/-- The norm of a factored arc displacement `↑(2·sin(δπ/12))·exp(↑θ·I)` equals
`2·sin(δπ/12)` for `0 < δ < 2`. Shared tail of the arc-norm lemmas at ρ and ρ+1.
@isnad1 id=eq.2h2v.s7.5cbce33b45e1 from=translated src=- shape=1cdf7e51 vocab=73ba6d84
-/
lemma norm_two_sin_mul_exp {δ θ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    ‖(↑(2 * Real.sin (δ * Real.pi / 12)) : ℂ) * Complex.exp (↑θ * I)‖ =
      2 * Real.sin (δ * Real.pi / 12) := by
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (by norm_num) (sin_delta_pi_div_twelve_pos hδ hδ2).le),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `0 < 2 · sin(π/12)`.
@isnad1 id=lt.0h0v.s5.e131e92e2c3a from=translated src=- shape=f3314f63 vocab=721197ad
-/
lemma two_sin_pi_div_twelve_pos : 0 < 2 * Real.sin (Real.pi / 12) := by
  linarith [sin_pi_div_twelve_pos]

/-- `arcsin(ε/2) < π/12` when `ε < 2 · sin(π/12)` and `−1 ≤ ε/2`.
@isnad1 id=lt.2h1v.s6.1f3adac62472 from=translated src=- shape=966e53e4 vocab=25431cb9
-/
lemma arcsin_half_lt_pi_div_twelve {ε : ℝ} (hε_half_neg : -1 ≤ ε / 2)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    Real.arcsin (ε / 2) < Real.pi / 12 :=
  calc Real.arcsin (ε / 2)
      < Real.arcsin (Real.sin (Real.pi / 12)) :=
        Real.arcsin_lt_arcsin hε_half_neg (by linarith) (Real.sin_le_one _)
    _ = Real.pi / 12 :=
        Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `12/π · arcsin(ε/2) < 1` for ε in the threshold range.
@isnad1 id=lt.2h1v.s6.f5ca12129c9b from=translated src=- shape=52d12bcf vocab=25431cb9
-/
lemma twelve_div_pi_arcsin_half_lt_one {ε : ℝ} (hε_half_neg : -1 ≤ ε / 2)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    12 / Real.pi * Real.arcsin (ε / 2) < 1 :=
  calc 12 / Real.pi * Real.arcsin (ε / 2)
      < 12 / Real.pi * (Real.pi / 12) :=
        mul_lt_mul_of_pos_left (arcsin_half_lt_pi_div_twelve hε_half_neg hε_lt_2sin)
          (div_pos (by norm_num) Real.pi_pos)
    _ = 1 := by field_simp

end
