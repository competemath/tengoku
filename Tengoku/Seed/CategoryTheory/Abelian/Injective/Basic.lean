/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Abelian.Exact
public import Tengoku.Seed.CategoryTheory.Preadditive.Injective.Basic
public import Tengoku.Seed.CategoryTheory.Preadditive.Yoneda.Limits
public import Tengoku.Seed.CategoryTheory.Preadditive.Yoneda.Injective
public import Tengoku.Seed.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Injective objects in abelian categories

* Objects in an abelian category are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/

public section


noncomputable section

open CategoryTheory Limits Injective Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The preadditive Yoneda functor on `J` preserves homology if `J` is injective.
@isnad1 id=preserve.0h2v.s6.638dc4f40f0e from=seed src=0 shape=4a995fd9 vocab=00af02e3
-/
instance preservesHomology_preadditiveYonedaObj_of_injective (J : C) [hJ : Injective J] :
    (preadditiveYonedaObj J).PreservesHomology := by
  let := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hJ
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/-- The preadditive Yoneda functor on `J` preserves colimits if `J` is injective.
@isnad1 id=preserve.0h2v.s5.b7aeff2ed9cf from=seed src=0 shape=4a995fd9 vocab=c74a6142
-/
instance preservesFiniteColimits_preadditiveYonedaObj_of_injective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/-- An object is injective if its preadditive Yoneda functor preserves finite colimits.
@isnad1 id=injectiv.0h2v.s5.319624362e33 from=seed src=0 shape=5b466ceb vocab=c74a6142
-/
theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

end CategoryTheory
