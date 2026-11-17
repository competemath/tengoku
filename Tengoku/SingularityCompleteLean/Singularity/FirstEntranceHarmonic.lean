import Tengoku.SingularityCompleteLean.Singularity.FirstEntrance
import Tengoku.SingularityCompleteLean.Singularity.StationaryCurrent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# First-hit bounds for nonnegative harmonic functions and stationary measures

Stopping at a single vertex gives F(x,y) h(y) ≤ h(x) for every nonnegative
superharmonic function. The proof uses finite-time entrance sums and their
proved convergence. Applied to the actual stationary Radon–Nikodym kernels,
it bounds a translated boundary measure by the original family of laws.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Finite first-hit sums are bounded by every nonnegative superharmonic function.
@isnad1 id=le.3h7v.s7.9028f1d01b5d from=translated src=- shape=43a8ce31 vocab=9681b602
-/
theorem firstEntrance_partial_superharmonic_bound
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (h : Γ → ℝ) (hp : ∀ x, 0 ≤ h x)
    (hh : ∀ x, ∑ g ∈ s, μ g * h (x * g) ≤ h x) (y : Γ) (N : ℕ) (x : Γ) :
    (∑ n ∈ Finset.range N, firstEntranceWeight s μ {y} n x y) * h y ≤ h x := by
  induction N generalizing x with
  | zero => simpa using hp x
  | succ N ih =>
    rw [Finset.sum_range_succ']
    by_cases hx : x = y
    · subst x
      simp only [firstEntranceWeight_succ_of_mem s μ {y} (mem_singleton y),
        Finset.sum_const_zero, firstEntranceWeight_zero, mem_singleton_iff, and_self,
        ite_true, zero_add, one_mul, le_refl]
    · have hxy : x ∉ ({y} : Set Γ) := hx
      simp_rw [firstEntranceWeight_succ_of_notMem s μ {y} hxy]
      rw [firstEntranceWeight_zero]
      simp only [hx, false_and, ite_false, add_zero]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_mul]
      calc
        _ ≤ ∑ g ∈ s, μ g * h (x * g) := by
          apply Finset.sum_le_sum
          intro g hg
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (ih (x * g)) (hμ g hg)
        _ ≤ h x := hh x

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- The full first-hit probability satisfies the optional-stopping inequality.
@isnad1 id=le.4h6v.s12.8367899e0021 from=translated src=- shape=85f6a327 vocab=cd8f5426
-/
theorem firstEntrance_superharmonic_bound
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (h : Γ → ℝ) (hp : ∀ x, 0 ≤ h x)
    (hh : ∀ x, ∑ g ∈ s, μ g * h (x * g) ≤ h x) (x y : Γ) :
    firstEntranceKernel s μ {y} x y * h y ≤ h x := by
  have ht := (firstEntranceWeight_summable s μ hμ hgap {y} x y).hasSum.tendsto_sum_nat.mul_const (h y)
  exact le_of_tendsto ht (Eventually.of_forall
    (fun N => firstEntrance_partial_superharmonic_bound s μ hμ h hp hh y N x))

end Singularity
