/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Algebra.Module.LinearMap.Defs
import Tengoku.Seed.Algebra.Module.NatInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

def toZLinearMap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [instA : Module ℤ A] [instB : Module ℤ B] (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    have hA : instA = AddCommGroup.toIntModule A := Subsingleton.elim _ _
    have hB : instB = AddCommGroup.toIntModule B := Subsingleton.elim _ _
    subst hA
    subst hB
    intro r x
    simp

@[simp]
theorem toZLinearMap_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (f : A →+ B) (a : A) : toZLinearMap f a = f a := rfl

end SRG266.Lattice
