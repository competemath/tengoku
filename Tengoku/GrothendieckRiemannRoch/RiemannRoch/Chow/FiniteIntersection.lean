/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.GradedCycles
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.Pullbacks
import Tengoku.Seed.RingTheory.Length

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Length cycles of finite scheme-theoretic intersections

For two closed subschemes of `X`, their scheme-theoretic intersection is their fiber product over
`X`. When this intersection has finitely many points and its local rings have finite length as
modules over the corresponding ambient local rings, those lengths define an actual algebraic
cycle on `X`. A codimension hypothesis on the intersection points makes it a homogeneous cycle.

This is the local-multiplicity brick needed for proper divisor intersections on a surface. It does
not yet construct Cartier divisors or prove invariance under rational equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Order
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Chow

/-- Length of the source local ring as a module over the target local ring at a point of a scheme
morphism.-/
noncomputable def morphismLocalLength {Z X : Scheme.{u}} (f : Z ⟶ X) (z : Z) : ℕ∞ :=
  letI : Algebra ↑(X.presheaf.stalk (f z)) ↑(Z.presheaf.stalk z) :=
    (f.stalkMap z).hom.toAlgebra
  Module.length ↑(X.presheaf.stalk (f z)) ↑(Z.presheaf.stalk z)

/-- Precomposing a scheme morphism by an isomorphism of its source preserves the local length.
@isnad1 id=eq.0h6v.s7.399108346357 from=translated src=- shape=66bdc964 vocab=7d2690eb
-/
theorem morphismLocalLength_comp_iso {W Z X : Scheme.{u}} (e : W ≅ Z)
    (f : Z ⟶ X) (w : W) :
    morphismLocalLength (e.hom ≫ f) w = morphismLocalLength f (e.hom w) := by
  unfold morphismLocalLength
  letI : Algebra ↑(X.presheaf.stalk ((e.hom ≫ f) w))
      ↑(Z.presheaf.stalk (e.hom w)) :=
    (f.stalkMap (e.hom w)).hom.toAlgebra
  letI : Algebra ↑(X.presheaf.stalk ((e.hom ≫ f) w)) ↑(W.presheaf.stalk w) :=
    ((e.hom ≫ f).stalkMap w).hom.toAlgebra
  let eAlg : ↑(Z.presheaf.stalk (e.hom w))
      ≃ₐ[↑(X.presheaf.stalk ((e.hom ≫ f) w))] ↑(W.presheaf.stalk w) :=
    AlgEquiv.ofRingEquiv
      (f := (asIso (e.hom.stalkMap w)).commRingCatIsoToRingEquiv) (by
        intro r
        change (e.hom.stalkMap w).hom ((f.stalkMap (e.hom w)).hom r) =
          ((e.hom ≫ f).stalkMap w).hom r
        rw [Scheme.Hom.stalkMap_comp]
        rfl)
  exact eAlg.toLinearEquiv.length_eq.symm

private theorem schemeHom_apply_eq_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    (h : f = g) (y : Y) : f y = g y := by
  exact ConcreteCategory.congr_hom (congrArg (fun q : Y ⟶ Z => q.base) h) y

/-- Geometric data for a finite scheme-theoretic intersection whose points all have codimension
`p` in the ambient scheme.-/
structure FiniteClosedIntersectionData (X : Scheme.{u}) (p : ℕ) where
  /-- First closed subscheme.-/
  D : Scheme.{u}
  /-- Second closed subscheme.-/
  E : Scheme.{u}
  /-- First closed immersion.-/
  i : D ⟶ X
  /-- Second closed immersion.-/
  j : E ⟶ X
  /-- The first morphism is a closed immersion.-/
  [closed_i : IsClosedImmersion i]
  /-- The second morphism is a closed immersion.-/
  [closed_j : IsClosedImmersion j]
  /-- The scheme-theoretic intersection has finitely many points.-/
  [finite_intersection :
    Finite ((CategoryTheory.Limits.pullback (C := Scheme.{u}) i j : Scheme.{u}) : Type u)]
  /-- Every local intersection length is finite.-/
  finiteLength : ∀ z : CategoryTheory.Limits.pullback (C := Scheme.{u}) i j,
    morphismLocalLength (CategoryTheory.Limits.pullback.fst i j ≫ i) z ≠ ⊤
  /-- Every intersection point maps to codimension `p` in `X`.-/
  codimension : ∀ z : CategoryTheory.Limits.pullback (C := Scheme.{u}) i j,
    coheight ((CategoryTheory.Limits.pullback.fst i j ≫ i) z) = p

attribute [instance]
  FiniteClosedIntersectionData.closed_i
  FiniteClosedIntersectionData.closed_j
  FiniteClosedIntersectionData.finite_intersection

namespace FiniteClosedIntersectionData

variable {X : Scheme.{u}} {p : ℕ} (d : FiniteClosedIntersectionData X p)

/-- The scheme-theoretic intersection.-/
abbrev intersection := CategoryTheory.Limits.pullback (C := Scheme.{u}) d.i d.j

/-- The canonical closed immersion of the intersection into the ambient scheme.-/
noncomputable def toX : d.intersection ⟶ X :=
  CategoryTheory.Limits.pullback.fst d.i d.j ≫ d.i

noncomputable instance : IsClosedImmersion d.toX := by
  dsimp only [toX]
  infer_instance

/-- The finite local intersection multiplicity.-/
noncomputable def localMultiplicity (z : d.intersection) : ℕ :=
  (morphismLocalLength d.toX z).toNat

/-- The local length is the natural-number intersection multiplicity, viewed in `ℕ∞`.
@isnad1 id=eq.0h4v.s5.005458ec8020 from=translated src=- shape=d481595b vocab=cbf51cb2
-/
theorem coe_localMultiplicity (z : d.intersection) :
    (d.localMultiplicity z : ℕ∞) = morphismLocalLength d.toX z := by
  exact ENat.natCast_toNat (d.finiteLength z)

/-- The length-weighted cycle of the finite scheme-theoretic intersection.-/
noncomputable def cycle : CodimensionCycles X ℤ p := by
  classical
  letI := Fintype.ofFinite d.intersection
  refine ⟨∑ z : d.intersection,
    Function.locallyFinsuppWithin.single (d.toX z) (d.localMultiplicity z : ℤ), ?_⟩
  intro x hx
  change (∑ z : d.intersection,
    Function.locallyFinsuppWithin.single (d.toX z) (d.localMultiplicity z : ℤ)) x ≠ 0 at hx
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at hx
  obtain ⟨z, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hxz : x = d.toX z := by
    by_contra h
    apply hz.2
    simp [Function.locallyFinsuppWithin.single_apply, h]
  subst x
  exact d.codimension z

/-- At an intersection point, the coefficient of the intersection cycle is its local length.
@isnad1 id=eq.0h4v.s9.642b7618868d from=translated src=- shape=15de0020 vocab=cc597cda
-/
@[simp]
theorem cycle_apply_toX (z : d.intersection) :
    d.cycle.1 (d.toX z) = (d.localMultiplicity z : ℤ) := by
  classical
  letI := Fintype.ofFinite d.intersection
  dsimp only [cycle]
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.single_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hwz
    have hne : d.toX z ≠ d.toX w := by
      intro h
      exact hwz (d.toX.isClosedEmbedding.injective h.symm)
    simp [hne]
  · simp

/-- The symmetry isomorphism between the two orders of the scheme-theoretic intersection.-/
noncomputable def intersectionSymmetry : d.intersection ≅
    CategoryTheory.Limits.pullback (C := Scheme.{u}) d.j d.i :=
  CategoryTheory.Limits.pullbackSymmetry d.i d.j

/-- The symmetry isomorphism followed by the original map to `X` is the exchanged map to `X`.
@isnad1 id=eq.0h3v.s7.f4fb04abd4c5 from=translated src=- shape=6f2d14c3 vocab=f53c5e19
-/
theorem intersectionSymmetry_inv_comp_toX :
    d.intersectionSymmetry.inv ≫ d.toX =
      CategoryTheory.Limits.pullback.fst d.j d.i ≫ d.j := by
  rw [toX, intersectionSymmetry, ← Category.assoc,
    CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst]
  exact (CategoryTheory.Limits.pullback.condition (f := d.j) (g := d.i)).symm

/-- The same finite closed intersection with its two factors exchanged.-/
noncomputable def swap : FiniteClosedIntersectionData X p := by
  let e := (Scheme.homeoOfIso d.intersectionSymmetry).toEquiv
  letI : Finite
      ((CategoryTheory.Limits.pullback (C := Scheme.{u}) d.j d.i : Scheme.{u}) : Type u) :=
    (Equiv.finite_iff e).mp inferInstance
  refine
    { D := d.E
      E := d.D
      i := d.j
      j := d.i
      finiteLength := ?_
      codimension := ?_ }
  · intro z
    rw [← d.intersectionSymmetry_inv_comp_toX]
    change morphismLocalLength (d.intersectionSymmetry.symm.hom ≫ d.toX) z ≠ ⊤
    rw [morphismLocalLength_comp_iso]
    exact d.finiteLength (d.intersectionSymmetry.inv z)
  · intro z
    rw [← d.intersectionSymmetry_inv_comp_toX]
    exact d.codimension (d.intersectionSymmetry.inv z)

/-- Exchanging the factors transports each local multiplicity along pullback symmetry.
@isnad1 id=eq.0h4v.s8.0f78a5512585 from=translated src=- shape=634d30af vocab=6c396676
-/
theorem swap_localMultiplicity
    (z : CategoryTheory.Limits.pullback (C := Scheme.{u}) d.j d.i) :
    d.swap.localMultiplicity z =
      d.localMultiplicity (d.intersectionSymmetry.inv z) := by
  change (morphismLocalLength
      (CategoryTheory.Limits.pullback.fst d.j d.i ≫ d.j) z).toNat =
    (morphismLocalLength d.toX (d.intersectionSymmetry.inv z)).toNat
  rw [← d.intersectionSymmetry_inv_comp_toX,
    show d.intersectionSymmetry.inv = d.intersectionSymmetry.symm.hom by rfl,
    morphismLocalLength_comp_iso]

/-- Pullback symmetry commutes with the maps of the two intersections to the ambient scheme.
@isnad1 id=eq.0h3v.s6.dcbf8912385e from=translated src=- shape=45be2939 vocab=38774106
-/
theorem intersectionSymmetry_hom_comp_swap_toX :
    d.intersectionSymmetry.hom ≫ d.swap.toX = d.toX := by
  change d.intersectionSymmetry.hom ≫
      (CategoryTheory.Limits.pullback.fst d.j d.i ≫ d.j) = d.toX
  rw [intersectionSymmetry, toX, ← Category.assoc,
    CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst]
  exact (CategoryTheory.Limits.pullback.condition (f := d.i) (g := d.j)).symm

/-- Local multiplicities agree at corresponding points under pullback symmetry.
@isnad1 id=eq.0h4v.s8.b69ecd62a669 from=translated src=- shape=9ad2aa63 vocab=fa4abd5e
-/
theorem swap_localMultiplicity_symmetry (z : d.intersection) :
    d.swap.localMultiplicity (d.intersectionSymmetry.hom z) = d.localMultiplicity z := by
  rw [d.swap_localMultiplicity]
  congr 1
  exact (Scheme.homeoOfIso d.intersectionSymmetry).left_inv z

/-- Every point of a finite scheme-theoretic intersection has positive local multiplicity.
@isnad1 id=lt.0h4v.s5.4cf99c16fe8c from=translated src=- shape=ea645f1b vocab=979f8308
-/
theorem localMultiplicity_pos (z : d.intersection) : 0 < d.localMultiplicity z := by
  letI : Algebra ↑(X.presheaf.stalk (d.toX z))
      ↑(d.intersection.presheaf.stalk z) :=
    (d.toX.stalkMap z).hom.toAlgebra
  apply ENat.toNat_pos
  · exact ne_of_gt (Module.length_pos :
      0 < morphismLocalLength d.toX z)
  · exact d.finiteLength z

end FiniteClosedIntersectionData

end AlgebraicGeometry.Chow
