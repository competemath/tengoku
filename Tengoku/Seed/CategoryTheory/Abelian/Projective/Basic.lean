/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Abelian.Exact
public import Tengoku.Seed.CategoryTheory.Preadditive.Yoneda.Projective
public import Tengoku.Seed.CategoryTheory.Preadditive.Yoneda.Limits
public import Tengoku.Seed.Algebra.Category.ModuleCat.EpiMono
public import Tengoku.Seed.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Projective objects in abelian categories

In an abelian category, an object `P` is projective iff the functor
`preadditiveCoyonedaObj P` preserves finite colimits.

-/

public section

universe v u

namespace CategoryTheory

open Limits Projective Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive co-Yoneda functor on `P` preserves homology if `P` is projective.
@isnad1 id=preserve.0h2v.s7.8b43b166c8d1 from=seed src=0 shape=6030706f vocab=5b8a1495
-/
noncomputable instance preservesHomology_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    (preadditiveCoyonedaObj P).PreservesHomology := by
  have := (projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).mp hP
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/-- The preadditive co-Yoneda functor on `P` preserves finite colimits if `P` is projective.
@isnad1 id=preserve.0h2v.s6.fa3c4f8e8729 from=seed src=0 shape=6030706f vocab=15722c9d
-/
noncomputable instance preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj P) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/-- An object is projective if its preadditive co-Yoneda functor preserves finite colimits.
@isnad1 id=projecti.0h2v.s6.c4baeb16f374 from=seed src=0 shape=49a55f12 vocab=15722c9d
-/
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj P)] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj]
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj P)
  infer_instance

end CategoryTheory
