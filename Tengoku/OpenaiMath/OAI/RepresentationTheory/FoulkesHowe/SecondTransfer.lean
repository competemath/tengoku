import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.EncodedCancellation
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.SecondCounts
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.SecondSwap
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.SecondEndpoints
import Tengoku.OpenaiMath.OAI.RepresentationTheory.FoulkesHowe.GridCancellation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Polynomial encoding preserves the independent factor permutations of each row. -/
theorem polynomial_row_permute {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : κ → V)
    (l : Fin (r+1) × Fin b → Block r)
    (σ : Fin (r+1) → Equiv.Perm (Fin b)) :
    multilinearPolynomial (flattenedSymmetricForm T) e
        (fun p => l (p.1, σ p.1 p.2)) =
      multilinearPolynomial (flattenedSymmetricForm T) e l := by
  apply MvPolynomial.funext
  intro z
  simp only [eval_multilinearPolynomial]
  exact flattenedSymmetricForm_inner_permute T σ
    (fun p => ∑ j : κ, z (l p,j) • e j)

end Problem346.SecondTransfer

end

end OAI
