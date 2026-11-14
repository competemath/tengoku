import Tengoku.Piirrationalitymeasure.Formalization.SaddleArc
import Tengoku.Piirrationalitymeasure.Formalization.PhaseCritical

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual complex saddle is the unique maximum on its controlled arc. -/

namespace PiIrrationality

noncomputable def holomorphicPhase (alpha beta : ℝ) (z : ℂ) : ℂ :=
  (alpha : ℂ) * Complex.log z + (beta : ℂ) * Complex.log (z ^ 2 + 6 * z + 25) -
    Complex.log (25 - z)

noncomputable def complexPhaseSlope (alpha beta : ℝ) (z : ℂ) : ℂ :=
  (alpha : ℂ) / z + (beta : ℂ) * (2 * z + 6) / (z ^ 2 + 6 * z + 25) + 1 / (25 - z)

theorem holomorphicPhase_re (alpha beta : ℝ) (z : ℂ) :
    (holomorphicPhase alpha beta z).re = complexPhase alpha beta z := by
  simp [holomorphicPhase, complexPhase, Complex.log_re]

theorem holomorphicPhase_hasDerivAt (alpha beta : ℝ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) (hq : z ^ 2 + 6 * z + 25 ∈ Complex.slitPlane)
    (hp : 25 - z ∈ Complex.slitPlane) :
    HasDerivAt (holomorphicPhase alpha beta) (complexPhaseSlope alpha beta z) z := by
  have hquad := (((hasDerivAt_id z).pow 2).add ((hasDerivAt_id z).const_mul 6)).add_const 25
  have hpole := (hasDerivAt_id z).const_sub 25
  have h := (((Complex.hasDerivAt_log hz).const_mul (alpha : ℂ)).add
    (((Complex.hasDerivAt_log hq).comp z hquad).const_mul (beta : ℂ))).sub
    ((Complex.hasDerivAt_log hp).comp z hpole)
  convert! h using 1
  dsimp [complexPhaseSlope]
  ring

theorem complexPhaseSlope_cleared {z : ℂ} (hz : z ≠ 0)
    (hq : z ^ 2 + 6 * z + 25 ≠ 0) (hp : 25 - z ≠ 0) :
    -5570 * z * (z ^ 2 + 6 * z + 25) * (25 - z) *
      complexPhaseSlope (1857 / 5570) (3714 / 5570) z =
        3715 * z ^ 3 - 232119 * z ^ 2 - 928475 * z - 1160625 := by
  unfold complexPhaseSlope
  push_cast
  have hq' : 25 + z * 6 + z ^ 2 ≠ 0 := by convert! hq using 1 <;> ring
  rw [show z ^ 2 + 6 * z + 25 = 25 + z * 6 + z ^ 2 by ring]
  field_simp [hz, hq, hq', hp]
  ring

theorem saddle_slitPlane_conditions :
    saddleUpper ∈ Complex.slitPlane ∧
      saddleUpper ^ 2 + 6 * saddleUpper + 25 ∈ Complex.slitPlane ∧
        25 - saddleUpper ∈ Complex.slitPlane := by
  have hi : 0 < saddleUpper.im := by simpa [saddleUpper] using saddleV_pos
  have hq : 0 < (saddleUpper ^ 2 + 6 * saddleUpper + 25).im := by
    have hu := saddleU_bounds.1
    have hv := saddleV_pos
    have he : (saddleUpper ^ 2 + 6 * saddleUpper + 25).im = (2 * saddleU + 6) * saddleV := by
      simp [saddleUpper, pow_two]
      ring
    rw [he]
    exact mul_pos (by linarith) hv
  refine ⟨Or.inr hi.ne', Or.inr hq.ne', Or.inr ?_⟩
  simpa using neg_ne_zero.mpr hi.ne'

theorem holomorphicPhase_saddle_hasDerivAt_zero :
    HasDerivAt (holomorphicPhase (1857 / 5570) (3714 / 5570)) 0 saddleUpper := by
  obtain ⟨hz, hq, hp⟩ := saddle_slitPlane_conditions
  have hz' := Complex.slitPlane_ne_zero hz
  have hq' := Complex.slitPlane_ne_zero hq
  have hp' := Complex.slitPlane_ne_zero hp
  have h := complexPhaseSlope_cleared hz' hq' hp'
  rw [stationaryCubic_saddleUpper] at h
  have hzero : complexPhaseSlope (1857 / 5570) (3714 / 5570) saddleUpper = 0 :=
    (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz') hq') hp')
  simpa only [hzero] using holomorphicPhase_hasDerivAt (1857 / 5570) (3714 / 5570) hz hq hp

theorem gammaPath_hasDerivAt (e t : ℝ) :
    HasDerivAt (gammaPath e)
      (((-3 : ℂ) + 4 * Complex.I) * (1 - Complex.I * (e : ℂ)) /
        (1 - Complex.I * (e : ℂ) * (1 - (t : ℂ))) ^ 2) t := by
  have hden := ((((hasDerivAt_id (t : ℂ)).const_sub 1).const_mul
    (Complex.I * (e : ℂ))).const_sub 1)
  have h := ((hasDerivAt_id (t : ℂ)).const_mul ((-3 : ℂ) + 4 * Complex.I)).div
    hden (gammaPath_den_ne_zero e t)
  convert! h.comp_ofReal using 1
  dsimp only [id_eq]
  field_simp
  ring

theorem complexPhase_saddle_arc_hasDerivAt_zero :
    HasDerivAt (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath saddleEta t))
      0 saddleLambda := by
  have hF := holomorphicPhase_saddle_hasDerivAt_zero
  rw [← saddle_arc_identity] at hF
  have h := hF.scomp saddleLambda (gammaPath_hasDerivAt saddleEta saddleLambda)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt saddleLambda h
  simpa only [Function.comp_def, smul_zero, Complex.reCLM_apply, Complex.zero_re,
    holomorphicPhase_re] using hr

noncomputable def saddleEtaLower : ℝ := 9102483223156522812 / 10 ^ 19
noncomputable def saddleEtaUpper : ℝ := 9102483223156522813 / 10 ^ 19

theorem saddleEta_paper_bounds : saddleEtaLower < saddleEta ∧ saddleEta < saddleEtaUpper := by
  have hu := saddleU_paper_bounds
  have hv := saddleV_paper_bounds
  have hm := saddleNormSq_paper_bounds
  dsimp [saddleULower, saddleUUpper] at hu
  dsimp [saddleVLower, saddleVUpper] at hv
  dsimp [saddleNormSqLower, saddleNormSqUpper] at hm
  have hd : 0 < -3 * saddleU + 4 * saddleV - saddleNormSq := by
    linarith [hu.1, hu.2, hv.1, hv.2, hm.1, hm.2]
  have he : saddleEta = -(4 * saddleU + 3 * saddleV) /
      (-3 * saddleU + 4 * saddleV - saddleNormSq) := by
    unfold saddleEta saddleY saddleX
    field_simp [saddleNormSq_pos.ne']
  rw [he]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    dsimp [saddleEtaLower]
    linarith [hu.1, hu.2, hv.1, hv.2, hm.1, hm.2]
  · apply (div_lt_iff₀ hd).mpr
    dsimp [saddleEtaUpper]
    linarith [hu.1, hu.2, hv.1, hv.2, hm.1, hm.2]

theorem saddleEta_gt_nine_tenths : (9 : ℝ) / 10 < saddleEta := by
  have h := saddleEta_paper_bounds.1
  norm_num [saddleEtaLower] at h
  linarith

theorem complexPhase_saddle_arc_strict_maximum (t : ℝ) (ht : t ∈ Set.Ioo 0 1)
    (hne : t ≠ saddleLambda) :
    complexPhase (1857 / 5570) (3714 / 5570) (gammaPath saddleEta t) <
      complexPhase (1857 / 5570) (3714 / 5570) saddleUpper := by
  have hroot := (complexPhase_on_arc_deriv_zero_iff saddleEta_gt_nine_tenths
    saddleLambda_mem.1 saddleLambda_mem.2).mp complexPhase_saddle_arc_hasDerivAt_zero.deriv
  simpa only [saddle_arc_identity] using complexPhase_on_arc_strict_max_of_root
    saddleEta_gt_nine_tenths saddleEta_lt_one saddleLambda_mem hroot t ht hne

theorem complexPhase_saddle_arc_le (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    complexPhase (1857 / 5570) (3714 / 5570) (gammaPath saddleEta t) ≤
      complexPhase (1857 / 5570) (3714 / 5570) saddleUpper := by
  by_cases he : t = saddleLambda
  · simp [he, saddle_arc_identity]
  · exact (complexPhase_saddle_arc_strict_maximum t ht he).le

end PiIrrationality
