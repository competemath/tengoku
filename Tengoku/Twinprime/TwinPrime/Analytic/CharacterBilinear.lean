import Tengoku.Twinprime.TwinPrime.Analytic.RationalLargeSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rectangular primitive-character bilinear first moments

Multiplicativity factors a sum over two fixed intervals. Weighted finite
Cauchy--Schwarz and the proved large sieve then bound its first moment.
These statements have no product cutoff and no maximum over endpoints;
neither operation is supplied by this rectangular estimate.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The explicit constant in the logarithmic primitive-character large sieve.-/
def characterLargeSieveConstant (Q M N : ℕ) : ℝ :=
  ((N - M : ℕ) : ℝ) + (Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1))

/-- Weighted Cauchy--Schwarz for two real sequences; zero weights are allowed.-/
theorem weighted_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι)
    (w f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i * g i) ≤
      Real.sqrt (∑ i ∈ s, w i * f i ^ 2) *
        Real.sqrt (∑ i ∈ s, w i * g i ^ 2) := by
  have hf : ∀ i ∈ s, 0 ≤ w i * f i ^ 2 :=
    fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hg : ∀ i ∈ s, 0 ≤ w i * g i ^ 2 :=
    fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hsq : (∑ i ∈ s, w i * f i * g i) ^ 2 ≤
      (∑ i ∈ s, w i * f i ^ 2) * ∑ i ∈ s, w i * g i ^ 2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hf hg
    intro i _
    exact le_of_eq (by ring)
  exact (Real.le_sqrt_of_sq_le hsq).trans_eq
    (Real.sqrt_mul (sum_nonneg hf) _)

/-- Multiplicativity factors a rectangular character sum exactly.-/
theorem character_rectangular_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ s, ∑ n ∈ t, a m * b n * χ (m * n)) =
      (∑ m ∈ s, a m * χ m) * ∑ n ∈ t, b n * χ n := by
  simp only [map_mul, sum_mul_sum]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  ring

end TwinPrime.Analytic
