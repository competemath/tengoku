import Tengoku.SingularityCompleteLean.Singularity.CountingKernel
import Tengoku.SingularityCompleteLean.Singularity.EntranceOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact entrance representations for L² harmonic functions

The actual first-entrance kernel represents every L² function harmonic outside
A. All sums, including for an infinite boundary A, are absolutely convergent.
This is the domain-exit representation needed for harmonic subtraction in
boundary Harnack arguments; no boundary Harnack comparison is assumed proved.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

/-- A first entrance cannot occur at a vertex outside the entrance set.
@isnad1 id=eq.1h6v.s5.73f54ec5be97 from=translated src=- shape=8510d4f8 vocab=c08a5600
-/
theorem firstEntranceKernel_eq_zero_of_notMem {Γ : Type*} [Group Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x a : Γ) (ha : a ∉ A) :
    firstEntranceKernel s μ A x a = 0 := by
  simp [firstEntranceKernel, firstEntranceWeight, ha]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

/-- Restrict boundary data and extend by the actual first-entrance operator.-/
def firstEntranceExtension : GroupL2 Γ →L[ℂ] GroupL2 Γ :=
  (entranceOperator s μ hμ hmass hgap A).comp (supportedRestriction A)

end Singularity
