import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Geometry
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The at-most-nine discarded t-values

The center-one count discards `t=0` and the roots of the eight
non-center linear forms.  With the center coefficient `0` included, all
nine bad values are uniformly represented by `-1 / λ`.
-/

/-- Candidate bad parameters: `0` (coming from the center coefficient)
and the at most eight values at which a non-center entry is zero.-/
def centerOneBadT (b : F) : Finset F :=
  Finset.univ.image (fun k : Fin 9 => (-1 : F) / centerOneCoeff b k)

omit [Fintype F] in
/-- There are at most nine discarded parameters.
@isnad1 id=le.0h2v.s4.5f2d3ffa2521 from=translated src=- shape=6cdb3b85 vocab=5c201bb0
-/
theorem centerOneBadT_card_le (b : F) :
    (centerOneBadT b).card ≤ 9 := by
  classical
  calc
    (centerOneBadT b).card ≤ (Finset.univ : Finset (Fin 9)).card :=
      Finset.card_image_le
    _ = 9 := by simp

omit [Fintype F] in
/-- Zero is always among the discarded parameters (via the center
coefficient `0`).
@isnad1 id=mem.0h2v.s5.a5ac20b0107a from=translated src=- shape=9674f620 vocab=527246e6
-/
theorem zero_mem_centerOneBadT (b : F) :
    0 ∈ centerOneBadT b := by
  classical
  refine Finset.mem_image.mpr ⟨(4 : Fin 9), by simp, ?_⟩
  simp [centerOneCoeff]

end Square3
end MagicSquares
