import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Complete
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.MultiplicityChoice
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.TSet
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma645.Complete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The concrete set estimate (6.28)

The set in Lemma 6.52 includes both the zeros of `f` and the points where
`B(g(c))=0`.  Applying the completed auxiliary-polynomial theorem to this
union, with the chosen integer multiplicity, gives (6.28).
-/

/-- The complete set `T` from Lemma 6.52, including the zeros of `f`.-/
noncomputable def stepanovFullT (m : ℕ) (f B : Polynomial F) : Finset F :=
  stepanovT0 f ∪ stepanovT B (stepanovG m f)

/--
@isnad1 id=iff.0h5v.s6.720dbfac0e55 from=translated src=- shape=377bde9d vocab=b71e3375
-/
@[simp] theorem mem_stepanovFullT (m : ℕ) (f B : Polynomial F) (c : F) :
    c ∈ stepanovFullT m f B ↔
      f.IsRoot c ∨ B.IsRoot (eval c (stepanovG m f)) := by
  simp [stepanovFullT, Polynomial.IsRoot]

end LN97
end MagicSquares
