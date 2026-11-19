import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.DegreeToCard
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The B-root part of the set in Lemma 6.52 and Theorem 6.53

This module records the points where `B(g(c))=0`.  The complete set in
Lemma 6.52 also includes the zeros of `f`; it is defined as
`stepanovFullT` in `SetBound`.
-/

/-- `T(B,g) = {c ∈ F_q | B(g(c)) = 0}`.-/
noncomputable def stepanovT
    (B g : Polynomial F) : Finset F := by
  classical
  exact Finset.univ.filter (fun c => B.IsRoot (eval c g))

/--
@isnad1 id=iff.0h4v.s6.d1222a739da7 from=translated src=- shape=c6eba0ba vocab=641f5821
-/
@[simp] theorem mem_stepanovT
    (B g : Polynomial F) (c : F) :
    c ∈ stepanovT B g ↔ B.IsRoot (eval c g) := by
  classical
  simp [stepanovT]

/-- Directly convert a Lemma-6.52 auxiliary polynomial into the basic
multiplicity count `M |T| ≤ deg h`.
@isnad1 id=le.2h5v.s6.0daf27c94902 from=translated src=- shape=6c1e9c04 vocab=a1f365c1
-/
theorem stepanovT_card_mul_le_natDegree
    (B g h : Polynomial F)
    (M : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c, B.IsRoot (eval c g) → M ≤ rootMultiplicity c h) :
    M * (stepanovT B g).card ≤ h.natDegree := by
  apply card_mul_le_natDegree_of_rootMultiplicity
    (F := F) h (stepanovT B g) M hM
  intro c hc
  exact hmult c ((mem_stepanovT B g c).mp hc)

end LN97
end MagicSquares
