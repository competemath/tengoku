/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.Grp
import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.Mod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parameter-dependent actions

A morphism `g : T ⟶ G` into a group object acting on `X` gives an automorphism of `T ⊗ X`:
it preserves the parameter and sends `(t, x)` to `(t, g(t) • x)`. Its inverse acts by `g(t)⁻¹`.
Named consumer: the generic translate on the function field of an actual regular curve action,
in the genus step of blueprint `lem:affine-action`.

**Status:** proved; the generic scheme-action consumer is in `SchemeGenericTranslate`.
The source arbitrary-action genus classification remains open.
-/

namespace CategoryTheory.ModObj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] (X : C) [ModObj G X] {T : C}

/-- Act on `X` while preserving the parameter. Named consumer: `parameterAut`.-/
def parameterAct (g : T ⟶ G) : T ⊗ X ⟶ T ⊗ X :=
  lift (fst T X) (((fst T X) ≫ g) • snd T X)

/--
@isnad1 id=eq.0h5v.s7.f3ad78996402 from=translated src=- shape=19b75b12 vocab=575d9219
-/
lemma parameterAct_fst (g : T ⟶ G) : parameterAct X g ≫ fst T X = fst T X :=
  lift_fst _ _

/--
@isnad1 id=eq.0h5v.s8.5719624dddd8 from=translated src=- shape=ae17a12a vocab=103d5c7a
-/
lemma parameterAct_snd (g : T ⟶ G) :
    parameterAct X g ≫ snd T X = ((fst T X) ≫ g) • snd T X :=
  lift_snd _ _

/--
@isnad1 id=eq.0h4v.s7.cfa467eafdd5 from=translated src=- shape=deee3e03 vocab=e91d4bb1
-/
lemma parameterAct_one : parameterAct X (1 : T ⟶ G) = 𝟙 (T ⊗ X) := by
  change lift (fst T X) (((fst T X) ≫ (1 : T ⟶ G)) • snd T X) = 𝟙 (T ⊗ X)
  rw [MonObj.comp_one, _root_.one_smul, lift_fst_snd]

/--
@isnad1 id=eq.0h6v.s8.c8b3c0238d07 from=translated src=- shape=27f15106 vocab=4d7b2ef6
-/
lemma parameterAct_mul (g h : T ⟶ G) :
    parameterAct X (g * h) = parameterAct X h ≫ parameterAct X g := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, parameterAct_fst]
  · rw [Category.assoc, parameterAct_snd, parameterAct_snd, comp_smul,
      ← Category.assoc, parameterAct_fst, parameterAct_snd, MonObj.comp_mul, smul_smul]

/-- Parameter-dependent group points act by automorphisms over the parameter.
Named consumer: the generic translate of a regular scheme action.-/
def parameterAut : (T ⟶ G) →* Aut (T ⊗ X) where
  toFun g :=
    { hom := parameterAct X g
      inv := parameterAct X g⁻¹
      hom_inv_id := by rw [← parameterAct_mul, inv_mul_cancel, parameterAct_one]
      inv_hom_id := by rw [← parameterAct_mul, mul_inv_cancel, parameterAct_one] }
  map_one' := Iso.ext (parameterAct_one X)
  map_mul' g h := Iso.ext (parameterAct_mul X g h)

end

end CategoryTheory.ModObj
