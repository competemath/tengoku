import Tengoku.Piirrationalitymeasure.Formalization.Saddle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The resultant identities and rational squared-modulus bounds in Appendix A.4. -/

namespace PiIrrationality

noncomputable def saddleQuadraticNormSq : ℝ :=
  Complex.normSq (saddleUpper ^ 2 + 6 * saddleUpper + 25)

noncomputable def saddlePoleNormSq : ℝ := Complex.normSq (25 - saddleUpper)

/--
@isnad1 id=eq.0h0v.s4.cb62c57dc888 from=translated src=- shape=501f93a1 vocab=635aa6d6
-/
theorem saddleUpper_normSq : Complex.normSq saddleUpper = saddleNormSq := by
  have hv := saddleV_sq
  unfold saddleVSq at hv
  simp [saddleUpper, Complex.normSq_apply]
  nlinarith

/--
@isnad1 id=eq.0h0v.s7.5f32dda2aa1f from=translated src=- shape=a48ea730 vocab=093a31b4
-/
theorem saddleQuadraticNormSq_eq :
    saddleQuadraticNormSq = saddleNormSq ^ 2 + 12 * saddleU * saddleNormSq +
      100 * saddleU ^ 2 + 300 * saddleU - 14 * saddleNormSq + 625 := by
  have h : saddleQuadraticNormSq = (saddleU ^ 2 + saddleV ^ 2) ^ 2 +
      12 * saddleU * (saddleU ^ 2 + saddleV ^ 2) +
      100 * saddleU ^ 2 + 300 * saddleU - 14 * (saddleU ^ 2 + saddleV ^ 2) + 625 := by
    simp [saddleQuadraticNormSq, saddleUpper, Complex.normSq_apply, pow_two]
    ring
  have huv : saddleU ^ 2 + saddleV ^ 2 = saddleNormSq := by
    have hv := saddleV_sq
    unfold saddleVSq at hv
    linarith
  rwa [huv] at h

/--
@isnad1 id=eq.0h0v.s5.bbd79c7061d7 from=translated src=- shape=b59935a2 vocab=eee08908
-/
theorem saddlePoleNormSq_eq :
    saddlePoleNormSq = 625 - 50 * saddleU + saddleNormSq := by
  have h : saddlePoleNormSq = 625 - 50 * saddleU + saddleU ^ 2 + saddleV ^ 2 := by
    simp [saddlePoleNormSq, saddleUpper, Complex.normSq_apply]
    ring
  have hv := saddleV_sq
  unfold saddleVSq at hv
  linarith

/--
@isnad1 id=eq.0h1v.s7.58d0247db71d from=translated src=- shape=d42d4864 vocab=5bef505a
-/
theorem stationaryCubic_quadratic_division (y : ℝ) :
    stationaryCubic y = (3715 * y - 254409) * (y ^ 2 + 6 * y + 25) +
      505104 * y + 5199600 := by
  unfold stationaryCubic
  ring

/--
@isnad1 id=eq.0h0v.s6.0576704c794c from=translated src=- shape=994ab632 vocab=fd3f62f3
-/
theorem saddleQuadraticNormSq_product :
    saddleQuadraticNormSq * (stationaryRoot ^ 2 + 6 * stationaryRoot + 25) =
      (706242355200 : ℝ) / 552049 := by
  have h : stationaryRoot ^ 2 *
      (saddleQuadraticNormSq * (552049 * (stationaryRoot ^ 2 + 6 * stationaryRoot + 25)) -
        706242355200) = stationaryCubic stationaryRoot *
          (stationaryCubic stationaryRoot + 237696 * stationaryRoot) := by
    rw [saddleQuadraticNormSq_eq]
    unfold saddleU saddleNormSq stationaryCubic
    field_simp [stationaryRoot_pos.ne']
    ring
  rw [stationaryRoot_eq_zero, zero_mul] at h
  have hz := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
    (pow_ne_zero 2 stationaryRoot_pos.ne'))
  linarith

/--
@isnad1 id=eq.0h0v.s6.a7e073031af1 from=translated src=- shape=1a8e3a08 vocab=fd3f62f3
-/
theorem saddleQuadraticNormSq_formula :
    saddleQuadraticNormSq = 706242355200 /
      (552049 * (stationaryRoot ^ 2 + 6 * stationaryRoot + 25)) := by
  have hd : 0 < 552049 * (stationaryRoot ^ 2 + 6 * stationaryRoot + 25) := by
    have hr := stationaryRoot_pos
    positivity
  apply (eq_div_iff hd.ne').mpr
  nlinarith [saddleQuadraticNormSq_product]

/--
@isnad1 id=eq.0h0v.s5.3534440e7a62 from=translated src=- shape=b077a574 vocab=de36e0aa
-/
theorem saddlePoleNormSq_formula :
    saddlePoleNormSq = 22280000 / (743 * (stationaryRoot - 25)) := by
  have hd : 0 < 743 * (stationaryRoot - 25) := by
    linarith [stationaryRoot_mem.1]
  apply (eq_div_iff hd.ne').mpr
  have h : stationaryRoot * (saddlePoleNormSq * (743 * (stationaryRoot - 25)) -
      22280000) = 5 * stationaryCubic stationaryRoot := by
    rw [saddlePoleNormSq_eq]
    unfold saddleU saddleNormSq stationaryCubic
    field_simp [stationaryRoot_pos.ne']
    ring
  rw [stationaryRoot_eq_zero, mul_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left stationaryRoot_pos.ne')

/--
@isnad1 id=and.0h0v.s8.f23952d41b51 from=translated src=- shape=26ca6ca0 vocab=96f81d58
-/
theorem saddleModuli_paper_bounds :
    ((4710661776618520503155596 : ℝ) / 10 ^ 24 < saddleNormSq ∧
      saddleNormSq < (4710661776618520503155597 : ℝ) / 10 ^ 24) ∧
    ((265339959117980760581398972 : ℝ) / 10 ^ 24 < saddleQuadraticNormSq ∧
      saddleQuadraticNormSq < (265339959117980760581398973 : ℝ) / 10 ^ 24) ∧
    ((725697065335997235474816912 : ℝ) / 10 ^ 24 < saddlePoleNormSq ∧
      saddlePoleNormSq < (725697065335997235474816913 : ℝ) / 10 ^ 24) := by
  have hrL := stationaryRoot_gt_rhoLower
  have hrU := stationaryRoot_lt_rhoUpper
  have hr0 := stationaryRoot_pos
  have hrL0 : 0 < rhoLower := by norm_num [rhoLower]
  have hqL : rhoLower ^ 2 + 6 * rhoLower + 25 ≤
      stationaryRoot ^ 2 + 6 * stationaryRoot + 25 := by gcongr
  have hqU : stationaryRoot ^ 2 + 6 * stationaryRoot + 25 ≤
      rhoUpper ^ 2 + 6 * rhoUpper + 25 := by gcongr
  have hdA : 0 < 552049 * (stationaryRoot ^ 2 + 6 * stationaryRoot + 25) := by positivity
  have hdJ : 0 < 743 * (stationaryRoot - 25) := by linarith [stationaryRoot_mem.1]
  have hm := saddleNormSq_paper_bounds
  norm_num [saddleNormSqLower, saddleNormSqUpper] at hm
  norm_num [rhoLower, rhoUpper] at hrL hrU hqL hqU
  refine ⟨⟨by linarith [hm.1], by linarith [hm.2]⟩, ?_, ?_⟩
  · rw [saddleQuadraticNormSq_formula]
    constructor
    · apply (lt_div_iff₀ hdA).mpr
      nlinarith [hqU]
    · apply (div_lt_iff₀ hdA).mpr
      nlinarith [hqL]
  · rw [saddlePoleNormSq_formula]
    constructor
    · apply (lt_div_iff₀ hdJ).mpr
      nlinarith [hrU]
    · apply (div_lt_iff₀ hdJ).mpr
      nlinarith [hrL]

end PiIrrationality
