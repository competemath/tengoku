/-
Assembly of the exact, unconditional finite-moment claim from proved components.
New implementation source, not compiled in the assistant environment.
This declaration has no arithmetic-discrepancy, CRT, or analytic premise.
-/
import Tengoku.Erdos647.Erdos647Sieve.ArithmeticDiscrepancy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve
open Bonferroni

/-- Finite-moment theorem with every protected parameter and hypothesis unchanged.-/
theorem finiteMoment : FiniteMomentClaim := by
  intro A X H y z J _hX hH hy hz0 hz1 hJ
  let I : Finset ℤ := Finset.Icc (A + 1) (A + (X : ℤ))
  let U : ℝ := ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
    (∑ n ∈ I, elementary (hitWeights H y z n) j)
  let V : ℝ := ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
    elementary (meanWeights H y z) j
  have hp : (∑ n ∈ I, z ^ hitCount H y n) ≤ U :=
    hitWeight_interval_upper A X H y z hz0 hz1 J hJ
  have hm : V ≤ Real.exp (-((1 - z) * primeMass H y)) +
      ((1 - z) * primeMass H y) ^ (J + 1) / (Nat.factorial (J + 1) : ℝ) :=
    meanWeight_truncation_upper H y z hz0 hz1 J hJ
  have heq :
      (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
        ((∑ n ∈ I, elementary (hitWeights H y z n) j) -
          (X : ℝ) * elementary (meanWeights H y z) j)) = U - (X : ℝ) * V := by
    dsimp only [U, V]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hd : |U - (X : ℝ) * V| ≤ ((H : ℝ) * y) ^ J := by
    rw [← heq]
    exact arithmetic_discrepancy_le A X H y z J hH hy hz0 hz1
  have hdu := (abs_le.mp hd).2
  have hXm := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg X)
  change (∑ n ∈ I, z ^ hitCount H y n) ≤
    (X : ℝ) * (Real.exp (-((1 - z) * primeMass H y)) +
      ((1 - z) * primeMass H y) ^ (J + 1) / (Nat.factorial (J + 1) : ℝ)) +
        ((H : ℝ) * y) ^ J
  linarith

end Erdos647Sieve
end
