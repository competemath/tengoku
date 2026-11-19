import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.TSet
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Equation (6.28): structural form before parameter simplification

Lemma 6.52 constructs `h` with multiplicity `M` on `T(B,g)` and an
upper degree bound.  This file records the immediate cardinality
consequence in the exact shape needed before the book substitutes its
specific choices of `u` and `M`.
-/

/-- Raw set estimate from an auxiliary polynomial.
@isnad1 id=le.3h6v.s7.a70523d3d6f1 from=translated src=- shape=0aebd877 vocab=a1f365c1
-/
theorem stepanovT_card_mul_le_of_auxiliary
    (B g h : Polynomial F)
    (M D : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c, B.IsRoot (eval c g) → M ≤ rootMultiplicity c h)
    (hdeg : h.natDegree ≤ D) :
    M * (stepanovT B g).card ≤ D := by
  exact le_trans
    (stepanovT_card_mul_le_natDegree
      (F := F) B g h M hM hmult)
    hdeg

/-- Division form of the raw estimate.
@isnad1 id=le.3h6v.s7.11668069da5f from=translated src=- shape=9c050748 vocab=b04a0dd5
-/
theorem stepanovT_card_le_div_of_auxiliary
    (B g h : Polynomial F)
    (M D : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c, B.IsRoot (eval c g) → M ≤ rootMultiplicity c h)
    (hdeg : h.natDegree ≤ D) :
    (stepanovT B g).card ≤ D / M := by
  apply (Nat.le_div_iff_mul_le hM).2
  simpa [Nat.mul_comm] using
    (stepanovT_card_mul_le_of_auxiliary
      (F := F) B g h M D hM hmult hdeg)

end LN97
end MagicSquares
