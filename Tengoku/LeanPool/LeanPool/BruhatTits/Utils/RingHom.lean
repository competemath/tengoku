/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Tengoku

/-!
# LeanPool.BruhatTits.Utils.RingHom
-/

@[expose] public section

open Module

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

-- up until line 70, this is now in mathlib (https://github.com/leanprover-community/mathlib4/pull/17433)
-- all in Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs.lean
-- for some reason `Units.map f.mapMatrix` does not work.
/-- Map an element of `GL` along a ring homomorphism. -/
def GL.map {α : Type*} [DecidableEq α] [Fintype α] (g : GL α R) : GL α S where
  val := f.mapMatrix g
  inv := f.mapMatrix g.inv
  val_inv := by rw [← map_mul]; simp
  inv_val := by rw [← map_mul]; simp
-- Matrix.GeneralLinearGroup.map

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
@isnad1 id=eq.0h5v.s7.5588a5580de0 from=translated src=- shape=ad60f819 vocab=380a5d23
-/
@[simp]
lemma GL.val_map (g : GL α R) : (GL.map f g).val = f.mapMatrix g.val := by
  rfl

/--
@isnad1 id=eq.0h7v.s7.25303e3f7967 from=translated src=- shape=8a5add4c vocab=ef5aaf8b
-/
@[simp]
lemma GL.map_apply (i j : α) (g : GL α R) : GL.map f g i j = f (g i j) := by
  rfl
--this is called Matrix.GeneralLinearGroup.map_apply and similarly for the ones below

/--
@isnad1 id=eq.0h4v.s7.53fb3cb71f65 from=translated src=- shape=f675fbe9 vocab=a16c2559
-/
lemma GL.map_one : GL.map f (1 : GL α R) = 1 := by
  ext i j
  simp [GL.map, Matrix.one_apply]

/--
@isnad1 id=eq.0h6v.s7.95fe18d41250 from=translated src=- shape=ed25c645 vocab=46efc352
-/
lemma GL.map_mul (g h : GL α R) : GL.map f (g * h) = GL.map f g * GL.map f h := by
  ext i j
  simp [GL.map, Matrix.mul_apply]

/--
@isnad1 id=eq.0h5v.s7.67740cb4ce81 from=translated src=- shape=027ae9b4 vocab=487ed28e
-/
lemma GL.map_inv (g : GL α R) : GL.map f g⁻¹ = (GL.map f g)⁻¹ := by
  ext i j
  rfl

/--
@isnad1 id=eq.0h5v.s9.fb1078e9f250 from=translated src=- shape=122ccb00 vocab=b475c2ad
-/
lemma GL.map_det (g : GL α R) : Matrix.GeneralLinearGroup.det (GL.map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  symm
  apply RingHom.map_det

/--
@isnad1 id=eq.0h5v.s7.1d7ddfb638c4 from=translated src=- shape=1bf6756b vocab=598cf56f
-/
lemma GL.map_mul_map_inv (g : GL α R) : GL.map f g * GL.map f g⁻¹ = 1 := by
  apply Units.ext
  simp_all

/--
@isnad1 id=eq.0h5v.s7.28bd3fb5c438 from=translated src=- shape=54316a15 vocab=598cf56f
-/
lemma GL.map_inv_mul_map (g : GL α R) : GL.map f g⁻¹ * GL.map f g = 1 := by
  apply Units.ext
  simp_all

/--
@isnad1 id=eq.0h5v.s8.a6345b80c9d5 from=translated src=- shape=65592334 vocab=4bef66fe
-/
lemma GL.coe_map_mul_map_inv (g : GL α R) : g.val.map f * g.val⁻¹.map f = 1 := by
  simp_all

/--
@isnad1 id=eq.0h5v.s8.099df44ea917 from=translated src=- shape=fc998df6 vocab=4bef66fe
-/
lemma GL.coe_map_inv_mul_map (g : GL α R) : g.val⁻¹.map f * g.val.map f = 1 := by
  simp_all

/--
@isnad1 id=eq.0h5v.s8.c96a4efcf0b5 from=translated src=- shape=92a5d35c vocab=33805dbd
-/
lemma GL_map_eq {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R S : Type*} [CommRing R] [CommRing S] (g : GL ι R) (f : R →+* S) :
    GL.map f g = Matrix.GeneralLinearGroup.map f g :=
  rfl

variable {K : Type*} [CommRing K] (R : Subring K)

/-- Coerce matrices over `R` to matrices over `K`. -/
instance instCoeHeadMatrixSubtypeMemSubringLeanPool {α β : Type*} :
    CoeHead (Matrix α β R) (Matrix α β K) where
  coe g := g.map R.subtype

/-- Coerce invertible matrices over `R` to matrices over `K`. -/
instance instCoeHeadGeneralLinearGroupSubtypeMemSubringLeanPool
    {α : Type*} [DecidableEq α] [Fintype α] : CoeHead (GL α R) (GL α K) where
  coe g := GL.map R.subtype g

--the following lemmas are used in CartanUniqueness.lean
/--
@isnad1 id=eq.0h4v.s9.8ffc3dc04762 from=translated src=- shape=12c96acc vocab=6406b6ce
-/
@[simp]
lemma Subring.coe_map_mul_map_inv (g : GL α R) :
    g.val.map Subtype.val * g.val⁻¹.map Subtype.val = 1 :=
  GL.coe_map_mul_map_inv R.subtype g

/--
@isnad1 id=eq.0h4v.s9.192e3f90ffbc from=translated src=- shape=076cf455 vocab=6406b6ce
-/
@[simp]
lemma Subring.coe_map_inv_mul_map (g : GL α R) :
    g.val⁻¹.map Subtype.val * g.val.map Subtype.val = 1 :=
  GL.coe_map_inv_mul_map R.subtype g

/--
@isnad1 id=eq.0h4v.s7.e88efa9171d7 from=translated src=- shape=b67fb54f vocab=4600c6d8
-/
@[simp]
lemma Subring.coe_det (g : Matrix α α R) : (g.map Subtype.val).det = g.det := by
  erw [← R.subtype.map_det]
  simp
