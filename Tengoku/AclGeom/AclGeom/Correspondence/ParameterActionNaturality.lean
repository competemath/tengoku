/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Correspondence.ParameterAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Changing the parameter of an actual action

Named consumer: base change of the tensor-coordinate action to the generic parameter and to
points of its affine parameter chart, in the finite coefficient-field producer of Lemma 8.4.

**Status:** proved; the actual coordinate consumer is `SchemeParameterBaseChange`.
-/

namespace CategoryTheory.ModObj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] (X : C) [ModObj G X] {S T : C}

/-- The parameter-preserving action commutes with changing the parameter.
Named consumer: literal tensor-coordinate base change for the actual generic coefficient field.
@isnad1 id=eq.0h7v.s8.1d0eec29afd6 from=translated src=- shape=d7c7f109 vocab=216507f6
-/
theorem parameterAct_natural (f : S ⟶ T) (g : T ⟶ G) :
    (f ⊗ₘ 𝟙 X) ≫ parameterAct X g = parameterAct X (f ≫ g) ≫ (f ⊗ₘ 𝟙 X) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, parameterAct_fst, tensorHom_fst]
    rw [← Category.assoc, parameterAct_fst]
  · simp only [Category.assoc, parameterAct_snd, tensorHom_snd, Category.comp_id,
      comp_smul, tensorHom_fst_assoc]

end

end CategoryTheory.ModObj
