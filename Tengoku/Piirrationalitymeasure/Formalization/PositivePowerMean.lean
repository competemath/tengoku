import Tengoku.Piirrationalitymeasure.Formalization.PositivePowerSeries
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientMean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Logarithmic slopes and positive saddle variance for general positive powers. -/

namespace PiIrrationality.PositivePower

noncomputable def mean (u v d : ℕ) (x : ℝ) : ℝ :=
  u * x / (1 + x) + v * (x * PRealPrime x) / PReal x + d * x / (1 - x)

noncomputable def meanPrime (u v d : ℕ) (x : ℝ) : ℝ :=
  u / (1 + x) ^ 2 + v * PMeanNumerator x / PReal x ^ 2 + d / (1 - x) ^ 2

noncomputable def saddleVariance (u v d : ℕ) (x : ℝ) : ℝ := x * deriv (mean u v d) x

theorem mean_hasDerivAt (u v d : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (mean u v d) (meanPrime u v d x) x := by
  have hp : 1 + x ≠ 0 := by linarith
  have hm : 1 - x ≠ 0 := by linarith
  have hP := (PReal_strictPositive x hx0).ne'
  have h := ((((hasDerivAt_id x).const_mul (u : ℝ)).div
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hp).add
    ((((hasDerivAt_id x).mul (PRealPrime_hasDerivAt x)).const_mul (v : ℝ)).div
      (PReal_hasDerivAt x) hP)).add
    (((hasDerivAt_id x).const_mul (d : ℝ)).div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hm)
  convert! h using 1
  dsimp [meanPrime, PMeanNumerator, PRealPrime, PReal]
  field_simp
  ring

theorem meanPrime_pos (u v : ℕ) {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 < meanPrime u v d x := by
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hP := PReal_strictPositive x hx0
  have hN := PMeanNumerator_pos hx0
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold meanPrime
  positivity

theorem mean_strictMono (u v : ℕ) {d : ℕ} (hd : 0 < d) :
    StrictMonoOn (mean u v d) (Set.Ico 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro x hx
    exact (mean_hasDerivAt u v d hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(mean_hasDerivAt u v d hx'.1 hx'.2).deriv]
    exact meanPrime_pos u v hd hx'.1 hx'.2

theorem saddleVariance_pos (u v : ℕ) {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < saddleVariance u v d x := by
  rw [saddleVariance, (mean_hasDerivAt u v d hx0.le hx1).deriv]
  exact mul_pos hx0 (meanPrime_pos u v hd hx0.le hx1)

theorem realValue_differentiableAt (u v d : ℕ) {x : ℝ} (hx1 : x < 1) :
    DifferentiableAt ℝ (realValue u v d) x := by
  have h : 1 - x ≠ 0 := by linarith
  unfold realValue PReal
  fun_prop (disch := exact pow_ne_zero _ h)

theorem log_realValue (u v d : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (realValue u v d x) =
      u * Real.log (1 + x) + v * Real.log (PReal x) - d * Real.log (1 - x) := by
  have hp : 1 + x ≠ 0 := by linarith
  have hm : 1 - x ≠ 0 := by linarith
  have hP := (PReal_strictPositive x hx0).ne'
  rw [realValue, Real.log_div (mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hP))
    (pow_ne_zero _ hm), Real.log_mul (pow_ne_zero _ hp) (pow_ne_zero _ hP),
    Real.log_pow, Real.log_pow, Real.log_pow]

end PiIrrationality.PositivePower
