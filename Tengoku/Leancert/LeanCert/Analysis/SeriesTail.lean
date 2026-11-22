import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Analysis.Normed.Group.InfiniteSum
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Quantitative series tails in complete normed additive groups.
The finite head is indexed by `range N`; the remainder starts at `N`. -/
namespace LeanCert.Analysis.SeriesTail

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- A summable majorant for the shifted tail proves summability of the whole
series and bounds the error after its first `N` terms. The head is unrestricted.
@isnad1 id=and.2h4v.s7.86ce62c87eee from=translated src=- shape=90802759 vocab=311b9d2e
-/
theorem of_majorant (f : ℕ → E) (N : ℕ) (g : ℕ → ℝ)
    (hg : Summable g) (hbound : ∀ k, ‖f (k + N)‖ ≤ g k) :
    Summable f ∧ ‖(∑' n, f n) - ∑ n ∈ Finset.range N, f n‖ ≤ ∑' k, g k := by
  have ht : Summable (fun k => f (k + N)) := hg.of_norm_bounded hbound
  have hf : Summable f := (summable_nat_add_iff N).mp ht
  refine ⟨hf, ?_⟩
  have he := hf.sum_add_tsum_nat_add N
  have hrem : (∑' n, f n) - ∑ n ∈ Finset.range N, f n = ∑' k, f (k + N) := by
    rw [← he]
    abel
  rw [hrem]
  exact tsum_of_norm_bounded hg.hasSum hbound

/-- Geometric domination of a tail, including ratio zero and an empty head.
This proves convergence, rather than assuming it in a certificate.
@isnad1 id=and.3h5v.s7.1e300b744436 from=translated src=- shape=5d48f9e1 vocab=56911255
-/
theorem of_geometric (f : ℕ → E) (N : ℕ) (A r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ k, ‖f (k + N)‖ ≤ A * r ^ k) :
    Summable f ∧ ‖(∑' n, f n) - ∑ n ∈ Finset.range N, f n‖ ≤ A / (1-r) := by
  have hg := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have h := of_majorant f N _ hg hbound
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv] using h

end LeanCert.Analysis.SeriesTail
