import Tengoku.PaperCLean.PaperC.Arithmetic.TerminalKernelCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Paper C v1.1: exact truncation in the defect count

Proposition 3.3 keeps the natural restriction that the product of the selected
small primes is at most the height `X` before applying Rankin's trick. This
file isolates that exact finite statement from the retained canonical kernel
decomposition.

No asymptotic estimate and no new external input is used here.
-/

namespace PaperC
namespace V11
namespace TruncatedDefectCount

open scoped BigOperators

open DefectCounting
open TerminalKernelCount

/-- Small-prime supports whose squarefree product can occur below `X`.-/
noncomputable def admissibleSmallSupports
    (B X : ℕ) : Finset (Finset ℕ) :=
  (smallPrimesUpTo B).powerset.filter fun small ↦
    small.prod id ≤ X

/--
@isnad1 id=iff.0h3v.s5.fc3097272685 from=translated src=- shape=3fd4a8c7 vocab=cc2a7146
-/
@[simp]
theorem mem_admissibleSmallSupports
    {B X : ℕ} {small : Finset ℕ} :
    small ∈ admissibleSmallSupports B X ↔
      small ⊆ smallPrimesUpTo B ∧ small.prod id ≤ X := by
  simp [admissibleSmallSupports]

/-- At terminal-kernel threshold `1`, the retained sigma count has one fibre.
@isnad1 id=le.0h2v.s5.014a9cb329f5 from=translated src=- shape=07501c40 vocab=e77861a0
-/
theorem card_kernel_one_le_unfiltered_sqrt_sum
    (B X : ℕ) :
    (boundedLargeKernelValues B 1 X).card ≤
      ∑ small ∈ (smallPrimesUpTo B).powerset,
        Nat.sqrt (X / small.prod id) := by
  simpa using card_boundedLargeKernelValues_le_sqrt_sum B 1 X

/-- The unfiltered square-root sum equals its restriction to admissible supports.
@isnad1 id=eq.0h2v.s5.e22b520eb668 from=translated src=- shape=3d1a7834 vocab=15f94bb5
-/
theorem sqrt_sum_eq_admissible_sum
    (B X : ℕ) :
    (∑ small ∈ (smallPrimesUpTo B).powerset,
        Nat.sqrt (X / small.prod id)) =
      ∑ small ∈ admissibleSmallSupports B X,
        Nat.sqrt (X / small.prod id) := by
  classical
  rw [admissibleSmallSupports, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro small hsmall
  by_cases hprod : small.prod id ≤ X
  · rw [ite_eq_left hprod]
  · rw [ite_eq_right hprod]
    have hlt : X < small.prod id := Nat.lt_of_not_ge hprod
    rw [Nat.div_eq_of_lt hlt]
    simp

/--
Exact truncated form of the defect count. The set on the left consists of
positive integers at most `X` whose large odd kernel above `B` is `1`.
@isnad1 id=le.0h2v.s5.4d9dc66d2298 from=translated src=- shape=a9c15af8 vocab=ee1d587c
-/
theorem card_kernel_one_le_truncated_sqrt_sum
    (B X : ℕ) :
    (boundedLargeKernelValues B 1 X).card ≤
      ∑ small ∈ admissibleSmallSupports B X,
        Nat.sqrt (X / small.prod id) := by
  rw [← sqrt_sum_eq_admissible_sum B X]
  exact card_kernel_one_le_unfiltered_sqrt_sum B X

end TruncatedDefectCount
end V11
end PaperC
