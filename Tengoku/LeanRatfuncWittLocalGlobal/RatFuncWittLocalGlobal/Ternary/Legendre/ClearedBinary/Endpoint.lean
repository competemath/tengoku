/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Ternary.Legendre.ClearedBinary.IsotropyBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cleared-binary endpoint
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/--
@isnad1 id=clearedb.1h3v.s8.8f888c733baa from=translated src=- shape=773d8ffe vocab=ab973489
-/
theorem clearedBinaryOrSquareRight_of_isSquare_neg_left
    {R : Type u} [Field R] {B C : Polynomial R}
    (hB : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B))) :
    ClearedBinaryOrSquareRight R B C :=
  (clearedBinaryOrSquareRight_iff_ternary_isotropic B C).mpr
    (Diagonal.ternary_isotropic_one_of_isSquare_neg_left hB)

/--
@isnad1 id=clearedb.2h3v.s9.0f7494c9f34e from=translated src=- shape=dc5b3458 vocab=c3f28191
-/
theorem clearedBinaryRight_of_isSquare_neg_left
    {R : Type u} [Field R] {B C : Polynomial R}
    (hB : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B)))
    (hC : ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C))) :
    ClearedBinaryRight R B C := by
  rcases (clearedBinaryOrSquareRight_iff_binary_or_square B C).mp
      (clearedBinaryOrSquareRight_of_isSquare_neg_left hB) with hbinary | hsquare
  · exact hbinary
  · exact False.elim (hC hsquare)

/--
@isnad1 id=iff.0h1v.s5.454e0221f34a from=translated src=- shape=6c04fe61 vocab=9d800e44
-/
theorem squarefreeBinaryConstructionRightNoObstruction_iff_nonterminal
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    SquarefreeBinaryConstructionRightNoObstruction.{u, v} R ↔
      SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R := by
  constructor
  · intro h B C hB hC hBsq hCsq hno _ hnotC
    exact h B C hB hC hBsq hCsq hno hnotC
  · intro h B C hB hC hBsq hCsq hno hnotC
    by_cases hsqB : IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B))
    · exact clearedBinaryRight_of_isSquare_neg_left hsqB hnotC
    · exact h B C hB hC hBsq hCsq hno hsqB hnotC

/--
@isnad1 id=squarefr.2h1v.s5.21bbce991431 from=translated src=- shape=4ff572b6 vocab=8df6d345
-/
theorem squarefreeNonterminalBinaryConstructionRightNoObstruction_of_noOrdering
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hreal : NormalizedOrderingRealization.{u, v} R)
    (h :
      SquarefreeNonterminalBinaryConstructionRightNoOrderingObstruction R) :
    SquarefreeNonterminalBinaryConstructionRightNoObstruction.{u, v} R := by
  intro B C hB hC hBsq hCsq hno hBterm hCterm
  exact h B C hB hC hBsq hCsq
    (by
      intro hord
      exact hno (hreal _ _ hord))
    hBterm hCterm

end RatFunc
end RatFuncWittLocalGlobal
