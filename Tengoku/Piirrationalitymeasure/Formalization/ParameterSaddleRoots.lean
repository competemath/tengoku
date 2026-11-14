import Tengoku.Piirrationalitymeasure.Formalization.ParameterComplexSaddle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The three actual roots and uniqueness of the chosen saddle branches near the candidate. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem parameterComplexSaddle_re (p : ℝ × ℝ) :
    (parameterComplexSaddle p).re = parameterSaddleU p := by simp [parameterComplexSaddle]

theorem parameterComplexSaddle_im (p : ℝ × ℝ) :
    (parameterComplexSaddle p).im = parameterSaddleV p := by simp [parameterComplexSaddle]

theorem parameterSaddle_quadratic_factorization {p : ℝ × ℝ}
    (hV : 0 ≤ parameterSaddleVSq p) (z : ℂ) :
    z ^ 2 - 2 * (parameterSaddleU p : ℂ) * z + (parameterSaddleNormSq p : ℂ) =
      (z - parameterComplexSaddle p) * (z - star (parameterComplexSaddle p)) := by
  have hv : parameterSaddleV p ^ 2 = parameterSaddleVSq p := Real.sq_sqrt hV
  unfold parameterSaddleVSq at hv
  apply Complex.ext <;> simp [parameterComplexSaddle, pow_two]
  · nlinarith only [hv]
  · ring

theorem parameterSaddle_roots_near_candidate : ∀ᶠ p in 𝓝 candidate,
    25 < parameterRealSaddle p ∧ 0 < (parameterComplexSaddle p).im ∧
      ∀ z : ℂ, parameterStationaryComplex p z = 0 ↔
        z = (parameterRealSaddle p : ℂ) ∨ z = parameterComplexSaddle p ∨
          z = star (parameterComplexSaddle p) := by
  have hA : ∀ᶠ p : ℝ × ℝ in 𝓝 candidate, 0 < p.1 + 2 * p.2 - 1 := by
    have hc : ContinuousAt (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) candidate := by fun_prop
    exact hc.eventually_const_lt (by norm_num [candidate])
  have hV : ∀ᶠ p in 𝓝 candidate, 0 < parameterSaddleVSq p :=
    contDiffAt_parameterSaddleVSq.continuousAt.eventually_const_lt
      (by rw [parameterSaddleVSq_candidate]; exact saddleVSq_pos)
  filter_upwards [hA, hV, parameterRealSaddle_near_candidate,
    parameterComplexSaddle_near_candidate] with p hAp hVp hrp hcp
  refine ⟨hrp.2, hcp.2, ?_⟩
  intro z
  rw [parameterStationaryComplex_factorization hAp.ne' (by linarith [hrp.2]) hrp.1,
    parameterSaddle_quadratic_factorization hVp.le]
  have hAc : ((p.1 + 2 * p.2 - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hAp.ne'
  simp only [mul_eq_zero, hAc, false_or, sub_eq_zero]

theorem parameterSaddle_unique_near_candidate : ∀ᶠ p in 𝓝 candidate,
    (∀ y : ℝ, parameterStationary p y = 0 ↔ y = parameterRealSaddle p) ∧
    (∀ z : ℂ, parameterStationaryComplex p z = 0 → 0 < z.im → z = parameterComplexSaddle p) := by
  filter_upwards [parameterSaddle_roots_near_candidate] with p hp
  obtain ⟨hr, hc, hroots⟩ := hp
  constructor
  · intro y
    constructor
    · intro hy
      have hyc : parameterStationaryComplex p y = 0 := by rw [parameterStationaryComplex_ofReal, hy]; simp
      rcases (hroots (y : ℂ)).mp hyc with he | he | he
      · exact_mod_cast he
      · have hi := congrArg Complex.im he
        simp only [Complex.ofReal_im] at hi
        linarith
      · have hi := congrArg Complex.im he
        simp only [Complex.ofReal_im, Complex.star_def, Complex.conj_im] at hi
        linarith
    · rintro rfl
      have h := (hroots (parameterRealSaddle p)).mpr (Or.inl rfl)
      rw [parameterStationaryComplex_ofReal] at h
      exact_mod_cast h
  · intro z hz hzi
    rcases (hroots z).mp hz with he | he | he
    · rw [he, Complex.ofReal_im] at hzi
      exact (lt_irrefl _ hzi).elim
    · exact he
    · rw [he] at hzi
      simp only [Complex.star_def, Complex.conj_im] at hzi
      linarith

end PiIrrationality
