import Tengoku.SquarefreeFugledeLean.FugledeAudit.BlockAlgebra
import Tengoku.SquarefreeFugledeLean.FugledeAudit.Integrality
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Ambient-support boundary

This file both composes the verified invariant-compression and integrality
steps, and checks an explicit counterexample to dropping invariance.
The counterexample is NOT a counterexample to the manuscript's theorem:
it is a test that the verification has not erased an essential hypothesis.
-/

namespace FugledeAudit

open Matrix

noncomputable def firewallProjection : Matrix (Fin 3) (Fin 3) ℂ := fun _ _ => 1 / 3
def firewallOperator : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
def firewallVector : Fin 3 → ℂ := ![1, 1, 1]

/-- An orthogonal compression of an integer matrix can have eigenvalue 1/3
without the ambient matrix having that eigenvector. Orthogonality of the
projection alone does not justify the integrality argument.-/
theorem compression_without_invariance_counterexample :
    firewallProjection * firewallProjection = firewallProjection ∧
    firewallProjection.conjTranspose = firewallProjection ∧
    firewallProjection.mulVec firewallVector = firewallVector ∧
    firewallVector ≠ 0 ∧
    firewallProjection.mulVec (firewallOperator.mulVec firewallVector) =
      ((1 : ℂ) / 3) • firewallVector ∧
    firewallOperator.mulVec firewallVector ≠ ((1 : ℂ) / 3) • firewallVector ∧
    (∀ i j, IsIntegral ℤ (firewallOperator i j)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    norm_num [firewallProjection, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    norm_num [firewallProjection, Matrix.conjTranspose_apply]
  · ext i
    fin_cases i <;>
      norm_num [firewallProjection, firewallVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
  · intro h
    have h₀ := congrArg (fun v : Fin 3 → ℂ => v 0) h
    norm_num [firewallVector] at h₀
  · ext i
    fin_cases i <;>
      norm_num [firewallProjection, firewallOperator, firewallVector, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  · intro h
    have h₀ := congrArg (fun v : Fin 3 → ℂ => v 0) h
    norm_num [firewallOperator, firewallVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h₀
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [firewallOperator, isIntegral_one, isIntegral_zero]

end FugledeAudit
