module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerLambda

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical parameters for the Witt design `S(5,8,24)`

This file records the concrete `λ_s` parameters for a Steiner system `S(5,8,24)`:
the numbers of blocks containing a given `s`-subset for `s = 1,2,3,4`, and the total number of
blocks.

Each statement is obtained from the general double-counting identity in `SteinerLambda.lean` by
plugging in `v = 24`, `k = 8`, `t = 5`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams

variable (S : SteinerSystem 24 8 5)

/-- A `4`-subset is contained in exactly `5` blocks of a Witt design.-/
public lemma card_blocksContaining_four (T : Finset (Fin 24)) (hT : T.card = 4) :
    (S.blocksContaining T).card = 5 := by
  have hmul :
      (S.blocksContaining T).card * Nat.choose (8 - 4) (5 - 4) =
        Nat.choose (24 - 4) (5 - 4) := by
    simpa [SteinerSystem.blocksContaining] using
      (SteinerSystem.card_blocksContaining_mul_choose (S := S) (T := T) (s := 4) hT (by decide))
  have h' : (S.blocksContaining T).card * 4 = 20 := by simpa using hmul
  exact Nat.mul_right_cancel (by decide : 0 < 4) (by simpa using h'.trans (by decide : 20 = 5 * 4))

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams
