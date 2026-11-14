import Tengoku.Piirrationalitymeasure.Formalization.ParameterConjugateData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual upper-half-plane saddle branch and its analytic regularity. -/

namespace PiIrrationality

open Filter
open scoped Topology ContDiff

noncomputable def parameterStationaryComplex (p : ℝ × ℝ) (z : ℂ) : ℂ :=
  ((p.1 + 2 * p.2 - 1 : ℝ) : ℂ) * z ^ 3 -
    ((19 * p.1 + 44 * p.2 + 6 : ℝ) : ℂ) * z ^ 2 -
    ((125 * p.1 + 150 * p.2 + 25 : ℝ) : ℂ) * z - ((625 * p.1 : ℝ) : ℂ)

noncomputable def parameterSaddleV (p : ℝ × ℝ) : ℝ := Real.sqrt (parameterSaddleVSq p)

noncomputable def parameterComplexSaddle (p : ℝ × ℝ) : ℂ :=
  (parameterSaddleU p : ℂ) + (parameterSaddleV p : ℂ) * Complex.I

theorem parameterStationaryComplex_ofReal (p : ℝ × ℝ) (y : ℝ) :
    parameterStationaryComplex p y = (parameterStationary p y : ℂ) := by
  unfold parameterStationaryComplex parameterStationary
  push_cast
  rfl

theorem parameterSaddleV_candidate : parameterSaddleV candidate = saddleV := by
  rw [parameterSaddleV, parameterSaddleVSq_candidate]
  rfl

theorem parameterComplexSaddle_candidate : parameterComplexSaddle candidate = saddleUpper := by
  rw [parameterComplexSaddle, parameterSaddleU_candidate, parameterSaddleV_candidate]
  rfl

theorem contDiffAt_parameterSaddleV : ContDiffAt ℝ ω parameterSaddleV candidate := by
  apply contDiffAt_parameterSaddleVSq.sqrt
  rw [parameterSaddleVSq_candidate]
  exact saddleVSq_pos.ne'

theorem analyticAt_parameterComplexSaddle : AnalyticAt ℝ parameterComplexSaddle candidate := by
  have hU : ContDiffAt ℝ ω (fun p => (parameterSaddleU p : ℂ)) candidate :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp candidate contDiffAt_parameterSaddleU
  have hV : ContDiffAt ℝ ω (fun p => (parameterSaddleV p : ℂ)) candidate :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp candidate contDiffAt_parameterSaddleV
  have hI : ContDiffAt ℝ ω (fun _ : ℝ × ℝ => Complex.I) candidate := contDiffAt_const
  exact (hU.add (hV.mul hI)).analyticAt

theorem parameterStationaryComplex_factorization {p : ℝ × ℝ}
    (hA : p.1 + 2 * p.2 - 1 ≠ 0) (hr : parameterRealSaddle p ≠ 0)
    (hroot : parameterStationary p (parameterRealSaddle p) = 0) (z : ℂ) :
    parameterStationaryComplex p z = ((p.1 + 2 * p.2 - 1 : ℝ) : ℂ) *
      (z - (parameterRealSaddle p : ℂ)) *
        (z ^ 2 - 2 * (parameterSaddleU p : ℂ) * z + (parameterSaddleNormSq p : ℂ)) := by
  obtain ⟨hsum, hpair, hprod⟩ := parameterSaddle_coefficients hA hr hroot
  have hsumC := congrArg Complex.ofReal hsum
  have hpairC := congrArg Complex.ofReal hpair
  have hprodC := congrArg Complex.ofReal hprod
  push_cast at hsumC hpairC hprodC
  unfold parameterStationaryComplex
  push_cast
  linear_combination z ^ 2 * hsumC - z * hpairC + hprodC

theorem parameterComplexSaddle_quadratic {p : ℝ × ℝ} (hp : 0 ≤ parameterSaddleVSq p) :
    parameterComplexSaddle p ^ 2 - 2 * (parameterSaddleU p : ℂ) * parameterComplexSaddle p +
      (parameterSaddleNormSq p : ℂ) = 0 := by
  have hv : parameterSaddleV p ^ 2 = parameterSaddleVSq p := Real.sq_sqrt hp
  apply Complex.ext <;>
    simp [parameterComplexSaddle, pow_two, Complex.mul_re, Complex.mul_im]
  · unfold parameterSaddleVSq at hv
    nlinarith only [hv]
  · ring

theorem parameterComplexSaddle_near_candidate : ∀ᶠ p in 𝓝 candidate,
    parameterStationaryComplex p (parameterComplexSaddle p) = 0 ∧
      0 < (parameterComplexSaddle p).im := by
  have hA : ∀ᶠ p : ℝ × ℝ in 𝓝 candidate, 0 < p.1 + 2 * p.2 - 1 := by
    have hc : ContinuousAt (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) candidate := by fun_prop
    exact hc.eventually_const_lt (by norm_num [candidate])
  have hV : ∀ᶠ p in 𝓝 candidate, 0 < parameterSaddleVSq p :=
    contDiffAt_parameterSaddleVSq.continuousAt.eventually_const_lt
      (by rw [parameterSaddleVSq_candidate]; exact saddleVSq_pos)
  filter_upwards [hA, hV, parameterRealSaddle_near_candidate] with p hAp hVp hrp
  constructor
  · rw [parameterStationaryComplex_factorization hAp.ne' (by linarith [hrp.2]) hrp.1,
      parameterComplexSaddle_quadratic hVp.le, mul_zero]
  · simpa only [parameterComplexSaddle, parameterSaddleV, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      using (Real.sqrt_pos.mpr hVp : 0 < parameterSaddleV p)

end PiIrrationality
