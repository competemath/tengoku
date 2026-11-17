import Tengoku.SingularityCompleteLean.Singularity.KilledWalk

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Translation of killed paths

Left multiplication preserves the jump word and its weight, while translating
both endpoints and the set to be avoided. The identities hold for finite
coefficients and their Green series without any convergence hypothesis.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Left multiplication transports the avoidance condition by preimage.
@isnad1 id=iff.0h7v.s6.2a2bb2c01ec1 from=translated src=- shape=0a010dae vocab=1b61fc58
-/
theorem avoidsBefore_left (s : Finset Γ) (A : Set Γ) (n : ℕ)
    (z x : Γ) (w : WalkWord s n) :
    avoidsBefore s A n (z * x) w ↔
      avoidsBefore s ((fun g => z * g) ⁻¹' A) n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [avoidsBefore, mul_assoc, ih, Set.mem_preimage]

/-- The killed transition kernel is covariant under simultaneous left translation.
@isnad1 id=eq.0h8v.s6.09eb53ecdb0e from=translated src=- shape=3785d599 vocab=17cd6b10
-/
theorem killedWeight_left (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ)
    (n : ℕ) (z x y : Γ) :
    killedWeight s μ A n (z * x) (z * y) =
      killedWeight s μ ((fun g => z * g) ⁻¹' A) n x y := by
  simp only [killedWeight, avoidsBefore_left, walkEndpoint_left,
    mul_left_cancel_iff, Set.mem_preimage]

/-- Left translation also transports the full killed Green series.
@isnad1 id=eq.0h7v.s6.9cdcf4d080a4 from=translated src=- shape=7c413d73 vocab=bc4653a1
-/
theorem killedGreen_left (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ)
    (z x y : Γ) :
    killedGreen s μ A (z * x) (z * y) =
      killedGreen s μ ((fun g => z * g) ⁻¹' A) x y := by
  simp only [killedGreen, killedWeight_left]

end Singularity
