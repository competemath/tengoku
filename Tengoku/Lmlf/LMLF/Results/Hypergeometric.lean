import Tengoku.Lmlf.LMLF.Definitions.Hypergeometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exceptional denominator shifts for the local Gauss hypergeometric series

The identities in this file concern the defining series on the open unit disk.  They do not
assert anything about an analytically continued branch.
-/

namespace LMLF.Definitions

private theorem regularizedGauss_neg_nat_coefficient_eq_zero
    (a b z : ℂ) (N s : ℕ) (hs : s < N + 1) :
    ((ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
        ((Nat.factorial s : ℂ) * Complex.Gamma (-(N : ℂ) + s))) * z ^ s = 0 := by
  have hsN : s ≤ N := by omega
  have harg : -(N : ℂ) + (s : ℂ) = -((N - s : ℕ) : ℂ) := by
    rw [Nat.cast_sub hsN]
    ring
  rw [harg, Complex.Gamma_neg_nat_eq_zero]
  simp

private theorem regularizedGauss_neg_nat_tail_coefficient
    (a b z : ℂ) (N k : ℕ) :
    ((ascPochhammer ℂ (k + (N + 1))).eval a *
          (ascPochhammer ℂ (k + (N + 1))).eval b /
        ((Nat.factorial (k + (N + 1)) : ℂ) *
          Complex.Gamma (-(N : ℂ) + (k + (N + 1))))) * z ^ (k + (N + 1)) =
      ((ascPochhammer ℂ (N + 1)).eval a *
          (ascPochhammer ℂ (N + 1)).eval b * z ^ (N + 1)) *
        (((ascPochhammer ℂ k).eval (a + ((N + 1 : ℕ) : ℂ)) *
              (ascPochhammer ℂ k).eval (b + ((N + 1 : ℕ) : ℂ)) /
            ((Nat.factorial k : ℂ) *
              Complex.Gamma (((N + 2 : ℕ) : ℂ) + k))) * z ^ k) := by
  have ha :
      (ascPochhammer ℂ (k + (N + 1))).eval a =
        (ascPochhammer ℂ (N + 1)).eval a *
          (ascPochhammer ℂ k).eval (a + ((N + 1 : ℕ) : ℂ)) := by
    have h := congrArg (Polynomial.eval a) (ascPochhammer_mul ℂ (N + 1) k)
    simpa [Nat.add_comm] using h.symm
  have hb :
      (ascPochhammer ℂ (k + (N + 1))).eval b =
        (ascPochhammer ℂ (N + 1)).eval b *
          (ascPochhammer ℂ k).eval (b + ((N + 1 : ℕ) : ℂ)) := by
    have h := congrArg (Polynomial.eval b) (ascPochhammer_mul ℂ (N + 1) k)
    simpa [Nat.add_comm] using h.symm
  have hgamma₁ :
      Complex.Gamma (-(N : ℂ) + ((k + (N + 1) : ℕ) : ℂ)) =
        (Nat.factorial k : ℂ) := by
    rw [show -(N : ℂ) + ((k + (N + 1) : ℕ) : ℂ) = (k : ℂ) + 1 by
      push_cast
      ring]
    exact Complex.Gamma_nat_eq_factorial k
  have hgamma₂ :
      Complex.Gamma (((N + 2 : ℕ) : ℂ) + (k : ℂ)) =
        (Nat.factorial (k + (N + 1)) : ℂ) := by
    rw [show ((N + 2 : ℕ) : ℂ) + (k : ℂ) =
        ((k + (N + 1) : ℕ) : ℂ) + 1 by
      push_cast
      ring]
    exact Complex.Gamma_nat_eq_factorial (k + (N + 1))
  rw [ha, hb]
  simp only [Nat.cast_add, Nat.cast_one] at hgamma₁ hgamma₂ ⊢
  rw [hgamma₁, hgamma₂, show k + (N + 1) = (N + 1) + k by omega,
    pow_add]
  ring

/-- The exceptional regularized Gauss series is a shifted regularized Gauss series on the source
disk.-/
theorem regularizedGaussHypergeometricSeriesSum_neg_nat
    {a b z : ℂ} (N : ℕ) (hz : ‖z‖ < 1) :
    regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ)) z =
      (ascPochhammer ℂ (N + 1)).eval a *
        (ascPochhammer ℂ (N + 1)).eval b * z ^ (N + 1) *
          regularizedGaussHypergeometricSeriesSum
            (a + ((N + 1 : ℕ) : ℂ))
            (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z := by
  let r : ℕ → ℂ := fun s ↦
    ((ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
        ((Nat.factorial s : ℂ) * Complex.Gamma (-(N : ℂ) + s))) * z ^ s
  let g : ℕ → ℂ := fun k ↦
    ((ascPochhammer ℂ k).eval (a + ((N + 1 : ℕ) : ℂ)) *
          (ascPochhammer ℂ k).eval (b + ((N + 1 : ℕ) : ℂ)) /
        ((Nat.factorial k : ℂ) * Complex.Gamma (((N + 2 : ℕ) : ℂ) + k))) * z ^ k
  let K : ℂ :=
    (ascPochhammer ℂ (N + 1)).eval a *
      (ascPochhammer ℂ (N + 1)).eval b * z ^ (N + 1)
  have hprefix : ∑ s ∈ Finset.range (N + 1), r s = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    exact regularizedGauss_neg_nat_coefficient_eq_zero a b z N s (Finset.mem_range.mp hs)
  have hshift : HasSum g
      (regularizedGaussHypergeometricSeriesSum
        (a + ((N + 1 : ℕ) : ℂ))
        (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z) := by
    exact hasSum_regularizedGaussHypergeometricSeries hz
  have htail : HasSum (fun k ↦ r (k + (N + 1)))
      (K * regularizedGaussHypergeometricSeriesSum
        (a + ((N + 1 : ℕ) : ℂ))
        (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z) := by
    apply (hshift.mul_left K).congr_fun
    intro k
    simpa only [r, g, K, Nat.cast_add, Nat.cast_one] using
      regularizedGauss_neg_nat_tail_coefficient a b z N k
  have hwhole : HasSum r
      ((∑ s ∈ Finset.range (N + 1), r s) +
        K * regularizedGaussHypergeometricSeriesSum
          (a + ((N + 1 : ℕ) : ℂ))
          (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z) :=
    htail.sum_range_add
  have hsource : HasSum r
      (regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ)) z) := by
    exact hasSum_regularizedGaussHypergeometricSeries hz
  have hunique := hsource.unique hwhole
  rw [hprefix, zero_add] at hunique
  simpa only [K, mul_assoc] using hunique

/-- The exceptional regularized Gauss series is a shifted ordinary Gauss series on the source
disk.-/
theorem regularizedGaussHypergeometricSeriesSum_neg_nat_eq_gauss
    {a b z : ℂ} (N : ℕ) (hz : ‖z‖ < 1) :
    regularizedGaussHypergeometricSeriesSum a b (-(N : ℂ)) z =
      ((ascPochhammer ℂ (N + 1)).eval a *
          (ascPochhammer ℂ (N + 1)).eval b * z ^ (N + 1) /
        (Nat.factorial (N + 1) : ℂ)) *
          gaussHypergeometricSeriesSum
            (a + ((N + 1 : ℕ) : ℂ))
            (b + ((N + 1 : ℕ) : ℂ)) ((N + 2 : ℕ) : ℂ) z := by
  have hc : ∀ n : ℕ, ((N + 2 : ℕ) : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hN : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hbridge := gaussHypergeometricSeriesSum_div_Gamma
    (a := a + ((N + 1 : ℕ) : ℂ)) (b := b + ((N + 1 : ℕ) : ℂ))
    (c := ((N + 2 : ℕ) : ℂ)) (z := z) hc hz
  have hgamma : Complex.Gamma (((N + 2 : ℕ) : ℂ)) =
      (Nat.factorial (N + 1) : ℂ) := by
    rw [show ((N + 2 : ℕ) : ℂ) = ((N + 1 : ℕ) : ℂ) + 1 by
      push_cast
      ring]
    exact Complex.Gamma_nat_eq_factorial (N + 1)
  rw [regularizedGaussHypergeometricSeriesSum_neg_nat N hz, ← hbridge, hgamma]
  ring

end LMLF.Definitions
