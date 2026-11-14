import Tengoku.Piirrationalitymeasure.Formalization.ParameterStationary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The real coefficients of the conjugate saddle branch in Section 6.7. -/

namespace PiIrrationality

open scoped ContDiff

noncomputable def parameterSaddleU (p : ℝ × ℝ) : ℝ :=
  ((19 * p.1 + 44 * p.2 + 6) / (p.1 + 2 * p.2 - 1) - parameterRealSaddle p) / 2

noncomputable def parameterSaddleNormSq (p : ℝ × ℝ) : ℝ :=
  625 * p.1 / ((p.1 + 2 * p.2 - 1) * parameterRealSaddle p)

noncomputable def parameterSaddleVSq (p : ℝ × ℝ) : ℝ :=
  parameterSaddleNormSq p - parameterSaddleU p ^ 2

theorem parameterSaddleU_candidate : parameterSaddleU candidate = saddleU := by
  rw [parameterSaddleU, parameterRealSaddle_candidate]
  norm_num [candidate, saddleU]

theorem parameterSaddleNormSq_candidate : parameterSaddleNormSq candidate = saddleNormSq := by
  rw [parameterSaddleNormSq, parameterRealSaddle_candidate]
  norm_num [candidate, saddleNormSq]
  field_simp

theorem parameterSaddleVSq_candidate : parameterSaddleVSq candidate = saddleVSq := by
  rw [parameterSaddleVSq, parameterSaddleNormSq_candidate, parameterSaddleU_candidate]
  rfl

theorem contDiffAt_parameterSaddleU : ContDiffAt ℝ ω parameterSaddleU candidate := by
  have hA : ContDiffAt ℝ ω (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) candidate := by fun_prop
  have hB : ContDiffAt ℝ ω (fun p : ℝ × ℝ => 19 * p.1 + 44 * p.2 + 6) candidate := by
    fun_prop
  have hA0 : candidate.1 + 2 * candidate.2 - 1 ≠ 0 := by norm_num [candidate]
  exact ((hB.div hA hA0).sub analyticAt_parameterRealSaddle.contDiffAt).div_const 2

theorem contDiffAt_parameterSaddleNormSq : ContDiffAt ℝ ω parameterSaddleNormSq candidate := by
  have hA : ContDiffAt ℝ ω (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) candidate := by fun_prop
  have hD : ContDiffAt ℝ ω (fun p : ℝ × ℝ => 625 * p.1) candidate := by fun_prop
  have hA0 : candidate.1 + 2 * candidate.2 - 1 ≠ 0 := by norm_num [candidate]
  have hr0 : parameterRealSaddle candidate ≠ 0 := by
    rw [parameterRealSaddle_candidate]
    exact stationaryRoot_pos.ne'
  exact hD.div (hA.mul analyticAt_parameterRealSaddle.contDiffAt) (mul_ne_zero hA0 hr0)

theorem contDiffAt_parameterSaddleVSq : ContDiffAt ℝ ω parameterSaddleVSq candidate :=
  contDiffAt_parameterSaddleNormSq.sub (contDiffAt_parameterSaddleU.pow 2)

theorem parameterSaddle_coefficients {p : ℝ × ℝ}
    (hA : p.1 + 2 * p.2 - 1 ≠ 0) (hr : parameterRealSaddle p ≠ 0)
    (hroot : parameterStationary p (parameterRealSaddle p) = 0) :
    (p.1 + 2 * p.2 - 1) * (2 * parameterSaddleU p + parameterRealSaddle p) =
        19 * p.1 + 44 * p.2 + 6 ∧
    (p.1 + 2 * p.2 - 1) *
        (parameterSaddleNormSq p + 2 * parameterRealSaddle p * parameterSaddleU p) =
        -(125 * p.1 + 150 * p.2 + 25) ∧
    (p.1 + 2 * p.2 - 1) * parameterRealSaddle p * parameterSaddleNormSq p = 625 * p.1 := by
  have hsum : (p.1 + 2 * p.2 - 1) *
      (2 * parameterSaddleU p + parameterRealSaddle p) = 19 * p.1 + 44 * p.2 + 6 := by
    unfold parameterSaddleU
    field_simp
    ring
  have hprod : (p.1 + 2 * p.2 - 1) * parameterRealSaddle p * parameterSaddleNormSq p =
      625 * p.1 := by
    unfold parameterSaddleNormSq
    field_simp
  refine ⟨hsum, ?_, hprod⟩
  apply mul_left_cancel₀ hr
  have hs := congrArg (fun t : ℝ => t * parameterRealSaddle p ^ 2) hsum
  unfold parameterStationary at hroot
  nlinarith only [hs, hprod, hroot]

end PiIrrationality
