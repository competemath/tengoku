/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import Tengoku.Seed.CategoryTheory.Triangulated.Functor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functoriality of the triangulated Grothendieck group

Triangulated functors induce homomorphisms on the repository-owned
Grothendieck group. Naturally isomorphic functors induce equal homomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v'

namespace CategoryTheory.Triangulated

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Object classes transported by a triangulated functor are
triangle-additive.
@isnad1 id=istriang.0h3v.s7.d67d1b8f9c53 from=translated src=- shape=8f99861f vocab=28bea131
-/
@[nolint unusedArguments]
instance K₀.isTriangleAdditive_map (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] : IsTriangleAdditive (fun X => K₀.of D (F.obj X)) where
  additive T hT := K₀.of_triangle D (F.mapTriangle.obj T) (F.map_distinguished T hT)

/-- The homomorphism on Grothendieck groups induced by a triangulated
functor.-/
def K₀.map (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] : K₀ C →+ K₀ D :=
  K₀.lift C (fun X => K₀.of D (F.obj X))

/--
@isnad1 id=eq.0h4v.s9.4bacc54faa00 from=translated src=- shape=365aff31 vocab=149b6cd9
-/
@[simp]
theorem K₀.map_of (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (X : C) : K₀.map F (K₀.of C X) = K₀.of D (F.obj X) :=
  K₀.lift_of C _ X

/--
@isnad1 id=eq.0h1v.s8.8ec6569b4992 from=translated src=- shape=704322d0 vocab=fbb8dec7
-/
@[simp]
theorem K₀.map_id : K₀.map (𝟭 C) = AddMonoidHom.id (K₀ C) := by
  ext X
  simp

/--
@isnad1 id=eq.0h5v.s9.fea04ae5c0fd from=translated src=- shape=ee2260d4 vocab=a8a28600
-/
@[simp]
theorem K₀.map_comp (F : C ⥤ D) {E : Type*} [Category E]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (G : D ⥤ E) [F.Additive] [G.Additive] [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] :
    K₀.map (F ⋙ G) = (K₀.map G).comp (K₀.map F) := by
  ext X
  simp

/-- Naturally isomorphic triangulated functors induce the same map on
Grothendieck groups.
@isnad1 id=eq.0h5v.s8.fe28c8158c2a from=translated src=- shape=1d7abdd4 vocab=8d2c5c12
-/
theorem K₀.map_congr {F G : C ⥤ D} [F.Additive] [G.Additive]
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (e : F ≅ G) : K₀.map F = K₀.map G := by
  ext X
  exact K₀.of_iso D (e.app X)

/-- A one-sided inverse of triangulated functors gives a one-sided inverse on
Grothendieck groups.
@isnad1 id=eq.0h5v.s9.6d9426bcf28d from=translated src=- shape=2ffd5e01 vocab=0c1936ee
-/
theorem K₀.map_comp_map_eq_id (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ]
    [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] (e : F ⋙ G ≅ 𝟭 C) :
    (K₀.map G).comp (K₀.map F) = AddMonoidHom.id (K₀ C) := by
  rw [← K₀.map_comp, K₀.map_congr e, K₀.map_id]

/-- **An exact equivalence induces an isomorphism on `K₀`.**

Stated from the two unit/counit isomorphisms rather than from `Equivalence`,
so that a caller who has a quasi-inverse triangulated functor in hand does not
first have to package it.-/
def K₀.mapAddEquiv (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (e : F ⋙ G ≅ 𝟭 C)
    (e' : G ⋙ F ≅ 𝟭 D) : K₀ C ≃+ K₀ D where
  toFun := K₀.map F
  invFun := K₀.map G
  map_add' := (K₀.map F).map_add
  left_inv x := by
    have := K₀.map_comp_map_eq_id F G e
    exact congrArg (fun f : K₀ C →+ K₀ C => f x) this
  right_inv y := by
    have := K₀.map_comp_map_eq_id G F e'
    exact congrArg (fun f : K₀ D →+ K₀ D => f y) this

/--
@isnad1 id=eq.0h7v.s10.cb33680d4644 from=translated src=- shape=4f4e2b6c vocab=d772231f
-/
@[simp]
theorem K₀.mapAddEquiv_apply (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ]
    [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] (e : F ⋙ G ≅ 𝟭 C)
    (e' : G ⋙ F ≅ 𝟭 D) (x : K₀ C) : K₀.mapAddEquiv F G e e' x = K₀.map F x :=
  rfl

end CategoryTheory.Triangulated
