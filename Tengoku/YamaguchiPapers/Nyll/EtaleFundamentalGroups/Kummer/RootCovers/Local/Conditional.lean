/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Iterated local root covers with trivial stages

After localizing at a prime, a boundary parameter outside that prime is a
unit.  Such a parameter must not be adjoined with a nontrivial root if one
wants the whole iterated cover to remain local.  The conditional presentation
used at a chosen prime gives those parameters exponent one.  A degree-one
stage is canonically the base ring, so it preserves both locality and the
residue field without requiring its radicand to lie in the maximal ideal.

The local-ring and faithful-flat structures below remain theorem-produced and
are installed only in proof scope.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- A degree-one root-adjunction is canonically the base algebra.-/
def adjoinRootOneAlgEquiv
    {R : Type u} [CommRing R] (a : R) :
    AdjoinRoot (X ^ 1 - C a) ≃ₐ[R] R := by
  refine (AdjoinRoot.algEquivOfEq R (X ^ 1 - C a) (X - C a) ?_).trans ?_
  · simp only [pow_one]
  · change (R[X] ⧸ Ideal.span ({X - C a} : Set R[X])) ≃ₐ[R] R
    exact Polynomial.quotientSpanXSubCAlgEquiv a

/-- The algebra map into a degree-one root-adjunction is bijective.
@isnad1 id=bijectiv.0h2v.s11.cec5229a9db2 from=translated src=- shape=345f2ccb vocab=1a75e1ab
-/
theorem algebraMap_bijective_adjoinRootOne
    {R : Type u} [CommRing R] (a : R) :
    Function.Bijective (algebraMap R (AdjoinRoot (X ^ 1 - C a))) := by
  let e := adjoinRootOneAlgEquiv a
  have he : (e.symm : R → AdjoinRoot (X ^ 1 - C a)) =
      algebraMap R (AdjoinRoot (X ^ 1 - C a)) := by
    funext x
    exact e.symm.commutes x
  rw [← he]
  exact e.symm.bijective

end EtaleFundamentalGroups.Kummer

end
