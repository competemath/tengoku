import Tengoku.Lmlf.LMLF.ODE.Hypergeometric.Principal
import Tengoku.Lmlf.LMLF.Results.Hypergeometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exceptional parameter results for the principal Gauss function

This downstream leaf lifts the local exceptional-denominator identities to the principal cut
plane. It also proves that early numerator termination makes the ambient regularized principal
function zero, including on the cut where the definition falls back to the original series sum.
-/

namespace LMLF.Definitions

private theorem regularizedGaussHypergeometricSeriesSum_eq_zero_of_early_left
    (b : ℂ) (m N : ℕ) (hm : m ≤ N) (z : ℂ) :
    regularizedGaussHypergeometricSeriesSum (-(m : ℂ)) b (-(N : ℂ)) z = 0 := by
  rw [regularizedGaussHypergeometricSeriesSum, Complex.regularizedGaussHGFun,
    FormalMultilinearSeries.sum]
  have hterms :
      (fun k : ℕ ↦
        (Complex.regularizedGaussHGFunSeries (-(m : ℂ)) b (-(N : ℂ)) k)
          (fun _ ↦ z)) = fun _ ↦ 0 := by
    funext k
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Complex.coeff_regularizedGaussHGFunSeries]
    have hcoeff :
        (ascPochhammer ℂ k).eval (-(m : ℂ)) * (ascPochhammer ℂ k).eval b /
            ((Nat.factorial k : ℂ) * Complex.Gamma (-(N : ℂ) + k)) = 0 := by
      by_cases hk : k ≤ N
      · have harg : -(↑N : ℂ) + (↑k : ℂ) = -((N - k : ℕ) : ℂ) := by
          rw [Nat.cast_sub hk]
          ring
        rw [harg, Complex.Gamma_neg_nat_eq_zero]
        simp
      · have hmk : m < k := lt_of_le_of_lt hm (lt_of_not_ge hk)
        rw [(@ascPochhammer_eval_neg_coe_nat_of_lt ℂ _ k m) hmk]
        simp
    rw [hcoeff]
    simp
  rw [hterms, tsum_zero]

private theorem regularizedGaussHypergeometricSeriesSum_eq_zero_of_early_right
    (a : ℂ) (m N : ℕ) (hm : m ≤ N) (z : ℂ) :
    regularizedGaussHypergeometricSeriesSum a (-(m : ℂ)) (-(N : ℂ)) z = 0 := by
  rw [regularizedGaussHypergeometricSeriesSum, Complex.regularizedGaussHGFun,
    FormalMultilinearSeries.sum]
  have hterms :
      (fun k : ℕ ↦
        (Complex.regularizedGaussHGFunSeries a (-(m : ℂ)) (-(N : ℂ)) k)
          (fun _ ↦ z)) = fun _ ↦ 0 := by
    funext k
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Complex.coeff_regularizedGaussHGFunSeries]
    have hcoeff :
        (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval (-(m : ℂ)) /
            ((Nat.factorial k : ℂ) * Complex.Gamma (-(N : ℂ) + k)) = 0 := by
      by_cases hk : k ≤ N
      · have harg : -(↑N : ℂ) + (↑k : ℂ) = -((N - k : ℕ) : ℂ) := by
          rw [Nat.cast_sub hk]
          ring
        rw [harg, Complex.Gamma_neg_nat_eq_zero]
        simp
      · have hmk : m < k := lt_of_le_of_lt hm (lt_of_not_ge hk)
        rw [(@ascPochhammer_eval_neg_coe_nat_of_lt ℂ _ k m) hmk]
        simp
    rw [hcoeff]
    simp
  rw [hterms, tsum_zero]

/-- The exceptional regularized principal Gauss function is a shifted principal Gauss function
throughout the cut plane.-/
theorem regularizedGaussHypergeometric_neg_nat
    {a b z : ℂ} (N : ℕ) (hz : z ∈ gaussHypergeometricDomain) :
    regularizedGaussHypergeometric a b (-(N : ℂ)) z =
      (ascPochhammer ℂ (N + 1)).eval a *
        (ascPochhammer ℂ (N + 1)).eval b * z ^ (N + 1) *
          regularizedGaussHypergeometric
            (a + ((N + 1 : ℕ) : ℂ))
            (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z := by
  let v : ℂ → ℂ := fun w ↦
    (ascPochhammer ℂ (N + 1)).eval a *
      (ascPochhammer ℂ (N + 1)).eval b * w ^ (N + 1) *
        regularizedGaussHypergeometric
          (a + ((N + 1 : ℕ) : ℂ))
          (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) w
  have hv : AnalyticOnNhd ℂ v gaussHypergeometricDomain := by
    exact ((analyticOnNhd_const.mul analyticOnNhd_const).mul
      (analyticOnNhd_id.pow (N + 1))).mul
        (regularizedGaussHypergeometric_analyticOnNhd
          (a + ((N + 1 : ℕ) : ℂ))
          (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ))
  have hvgerm : Set.EqOn v
      (regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ))) (Metric.ball 0 1) := by
    intro w hw
    dsimp only [v]
    rw [regularizedGaussHypergeometric_eqOn_seriesSum
      (a + ((N + 1 : ℕ) : ℂ))
      (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) hw]
    exact (regularizedGaussHypergeometricSeriesSum_neg_nat N (by simpa using hw)).symm
  exact regularizedGaussHypergeometric_eqOn_of_eqOn_seriesSum
    a b (-(N : ℂ)) hv hvgerm hz

/-- The exceptional regularized principal Gauss function is a shifted ordinary principal Gauss
function, with the positive-integer Gamma value written as a factorial.-/
theorem regularizedGaussHypergeometric_neg_nat_eq_gauss
    {a b z : ℂ} (N : ℕ) (hz : z ∈ gaussHypergeometricDomain) :
    regularizedGaussHypergeometric a b (-(N : ℂ)) z =
      ((ascPochhammer ℂ (N + 1)).eval a *
          (ascPochhammer ℂ (N + 1)).eval b * z ^ (N + 1) /
        (Nat.factorial (N + 1) : ℂ)) *
          gaussHypergeometric
            (a + ((N + 1 : ℕ) : ℂ))
            (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z := by
  have hc : ∀ n : ℕ, ((N + 2 : ℕ) : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hN : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hbridge := gaussHypergeometric_div_Gamma
    (a := a + ((N + 1 : ℕ) : ℂ)) (b := b + ((N + 1 : ℕ) : ℂ))
    (c := ((N + 2 : ℕ) : ℂ)) hc z
  have hgamma : Complex.Gamma (((N + 2 : ℕ) : ℂ)) =
      (Nat.factorial (N + 1) : ℂ) := by
    rw [show ((N + 2 : ℕ) : ℂ) = ((N + 1 : ℕ) : ℂ) + 1 by
      push_cast
      ring]
    exact Complex.Gamma_nat_eq_factorial (N + 1)
  rw [regularizedGaussHypergeometric_neg_nat N hz, ← hbridge, hgamma]
  ring

/-- If the left numerator terminates no later than an exceptional denominator, the ambient
regularized principal Gauss function is identically zero, including on the branch cut.-/
theorem regularizedGaussHypergeometric_eq_zero_of_early_left_termination
    (b : ℂ) (m N : ℕ) (hm : m ≤ N) (z : ℂ) :
    regularizedGaussHypergeometric (-(m : ℂ)) b (-(N : ℂ)) z = 0 := by
  by_cases hz : z ∈ gaussHypergeometricDomain
  · rw [regularizedGaussHypergeometric_neg_nat N hz,
      (@ascPochhammer_eval_neg_coe_nat_of_lt ℂ _ (N + 1) m) (by omega)]
    simp
  · rw [regularizedGaussHypergeometric_eqOn_seriesSum_compl
      (-(m : ℂ)) b (-(N : ℂ)) (by simpa using hz)]
    exact regularizedGaussHypergeometricSeriesSum_eq_zero_of_early_left b m N hm z

/-- If the right numerator terminates no later than an exceptional denominator, the ambient
regularized principal Gauss function is identically zero, including on the branch cut.-/
theorem regularizedGaussHypergeometric_eq_zero_of_early_right_termination
    (a : ℂ) (m N : ℕ) (hm : m ≤ N) (z : ℂ) :
    regularizedGaussHypergeometric a (-(m : ℂ)) (-(N : ℂ)) z = 0 := by
  by_cases hz : z ∈ gaussHypergeometricDomain
  · rw [regularizedGaussHypergeometric_neg_nat N hz,
      (@ascPochhammer_eval_neg_coe_nat_of_lt ℂ _ (N + 1) m) (by omega)]
    simp
  · rw [regularizedGaussHypergeometric_eqOn_seriesSum_compl
      a (-(m : ℂ)) (-(N : ℂ)) (by simpa using hz)]
    exact regularizedGaussHypergeometricSeriesSum_eq_zero_of_early_right a m N hm z

end LMLF.Definitions
