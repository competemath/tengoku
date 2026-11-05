/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.AlgebraicGeometry.FunctionField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Function fields of dominant morphisms

A morphism with dense image between integral schemes sends the generic point
to the generic point.  Its map on local rings therefore gives the canonical
embedding of function fields.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  exact (Z.presheaf.stalkSpecializes_refl z).symm

/-- A dense morphism between irreducible schemes sends the generic point to
the generic point.
@isnad1 id=eq.1h3v.s8.079c3555735c from=translated src=- shape=b6aa5a16 vocab=52966a6c
-/
theorem map_genericPoint_of_denseRange
    (f : Y ⟶ X) [IrreducibleSpace X] [IrreducibleSpace Y]
    (hf : DenseRange f) :
    f (genericPoint Y) = genericPoint X := by
  apply ((genericPoint_spec X).eq _).symm
  convert (genericPoint_spec Y).image f.continuous using 1
  simpa only [Set.image_univ] using hf.closure_range.symm

/-- The canonical map on function fields induced by a dense morphism of
integral schemes.-/
noncomputable def functionFieldMap
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    X.functionField →+* Y.functionField :=
  (eqToHom (show
      X.presheaf.stalk (genericPoint X) =
        X.presheaf.stalk (f (genericPoint Y)) by
      rw [map_genericPoint_of_denseRange f hf]) ≫
    f.stalkMap (genericPoint Y)).hom

/-- The function-field map of a dense morphism of integral schemes is
injective.
@isnad1 id=injectiv.1h3v.s8.b461d55e409a from=translated src=- shape=f96664c9 vocab=20b32d16
-/
theorem functionFieldMap_injective
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    Function.Injective (functionFieldMap f hf) :=
  (functionFieldMap f hf).injective

/-- On global sections, the function-field map of a dense morphism is the
map obtained by first pulling back the section and then taking its germ at
the generic point.
@isnad1 id=other.1h3v.s12.64444238d8dc from=translated src=- shape=ce8b8156 vocab=90e786e5
-/
theorem functionFieldMap_comp_germToFunctionField_top
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    let _ : Nonempty (⊤ : X.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty X), by trivial⟩⟩
    let _ : Nonempty (⊤ : Y.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty Y), by trivial⟩⟩
    (functionFieldMap f hf).comp (X.germToFunctionField ⊤).hom =
      (Y.germToFunctionField ⊤).hom.comp f.appTop.hom := by
  intro nonemptyX nonemptyY
  let h : genericPoint X = f (genericPoint Y) :=
    (map_genericPoint_of_denseRange f hf).symm
  have hEq : eqToHom (show
      X.presheaf.stalk (genericPoint X) =
        X.presheaf.stalk (f (genericPoint Y)) by
      rw [map_genericPoint_of_denseRange f hf]) =
      (X.presheaf.stalkCongr (.of_eq h)).hom := by
    convert eqToHom_stalk_eq_stalkCongr X h
  unfold functionFieldMap
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  apply congrArg CommRingCat.Hom.hom
  rw [hEq]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap ⊤ (genericPoint Y) (by trivial)

/-- The algebra structure on the target function field induced by a dense
morphism of integral schemes.-/
@[reducible] noncomputable def functionFieldAlgebraOfDenseRange
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    Algebra X.functionField Y.functionField :=
  (functionFieldMap f hf).toAlgebra

end Scheme.Hom

end AlgebraicGeometry
