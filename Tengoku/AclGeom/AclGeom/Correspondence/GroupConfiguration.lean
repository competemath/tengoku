/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Correspondence.GroupChunk
import Tengoku.Seed.CategoryTheory.Groupoid.VertexGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The six-point group-configuration bookkeeping

The group-theoretic identities in the final part of blueprint Theorem
`six-point-group`, separated from the geometric extraction of the group:

* a genuine three-object groupoid transports its vertex group to a
  `RationalGroupChunk` on every based arrow family;
* `differenceChart e a = e⁻¹a` is the chart based at the generic arrow `e`;
* `differenceChart_mul` and `differenceChart_inv` compute multiplication and
  inverse in that chart;
* `groupoidComposite_eq` is the four-arrow cancellation calculation used to
  prove closure of the chart;
* `sixPointGroupTuple α γ ε` is the ordered sextuple
  `(α, γ, αγ, ε, αγε, γε)`, and
  `sixPointGroupTuple_relations` proves its four named product relations.

The groupoid lemmas formalize the exact four-arrow cancellation before
algebraization; the group lemmas give its normalized output.  The
still-geometric part of the blueprint theorem must construct the genuine
groupoid from the finite-cover correspondence components.

**Status:** complete algebraic bookkeeping for M4a / blueprint (8.3); the
geometric six-point extraction remains in progress.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open CategoryTheory

section GroupoidDifferenceChart

variable {C : Type*} [CategoryTheory.Groupoid C] {X Y Z : C}

/-- The difference chart of arrows in a genuine groupoid.  For base and
variable arrows `e,a : X ⟶ Y`, it is the vertex-group element obtained by
following `a` with `e⁻¹`.  This is the categorical form of `e⁻¹a` in the
blueprint's functional-composition convention.-/
def groupoidDifferenceChart (e a : X ⟶ Y) : X ⟶ X :=
  a ≫ inv e

/-- Functors between groupoids preserve based difference charts.-/
theorem map_groupoidDifferenceChart
    {D : Type*} [CategoryTheory.Groupoid D] (F : C ⥤ D)
    (e a : X ⟶ Y) :
    F.map (groupoidDifferenceChart e a) =
      groupoidDifferenceChart (F.map e) (F.map a) := by
  simp [groupoidDifferenceChart, CategoryTheory.Functor.map_inv]

/-- A based difference chart is the identity exactly at its base arrow.-/
theorem groupoidDifferenceChart_eq_one_iff (e a : X ⟶ Y) :
    groupoidDifferenceChart e a = 1 ↔ a = e := by
  constructor
  · intro h
    apply (cancel_mono (inv e)).1
    simpa [groupoidDifferenceChart] using h
  · rintro rfl
    simp [groupoidDifferenceChart]

/-- The arrow-family parameter representing the product of two groupoid
difference-chart elements.-/
def groupoidDifferenceProduct (e a b : X ⟶ Y) : X ⟶ Y :=
  a ≫ inv e ≫ b

/-- Functors between groupoids preserve the difference-product expression
on every based arrow family.-/
theorem map_groupoidDifferenceProduct
    {D : Type*} [CategoryTheory.Groupoid D] (F : C ⥤ D)
    (e a b : X ⟶ Y) :
    F.map (groupoidDifferenceProduct e a b) =
      groupoidDifferenceProduct (F.map e) (F.map a) (F.map b) := by
  simp [groupoidDifferenceProduct, CategoryTheory.Functor.map_inv]

/-- Inverting every arrow converts a difference product into the inverse
of the product with its two variable inputs exchanged.-/
theorem groupoidDifferenceProduct_inv (e a b : X ⟶ Y) :
    groupoidDifferenceProduct (inv e) (inv a) (inv b) =
      inv (groupoidDifferenceProduct e b a) := by
  simp [groupoidDifferenceProduct, Category.assoc, IsIso.inv_comp]

/-- Multiplication in the vertex group is closed in the difference chart,
with the parameter formula `a e⁻¹ b`.-/
theorem groupoidDifferenceChart_mul (e a b : X ⟶ Y) :
    groupoidDifferenceChart e a * groupoidDifferenceChart e b =
      groupoidDifferenceChart e (groupoidDifferenceProduct e a b) := by
  simp only [groupoidDifferenceChart, groupoidDifferenceProduct,
    CategoryTheory.Groupoid.vertexGroup_mul, Category.assoc]

/-- The arrow-family parameter representing the inverse of a difference-
chart element.-/
def groupoidDifferenceInverse (e a : X ⟶ Y) : X ⟶ Y :=
  e ≫ inv a ≫ e

/-- Inversion in the vertex group is closed in the difference chart.-/
theorem groupoidDifferenceChart_inv (e a : X ⟶ Y) :
    (groupoidDifferenceChart e a)⁻¹ =
      groupoidDifferenceChart e (groupoidDifferenceInverse e a) := by
  simp [groupoidDifferenceChart, groupoidDifferenceInverse,
    CategoryTheory.Groupoid.vertexGroup_inv, Category.assoc]

/-- The four-arrow cancellation from blueprint (8.3), stated in a genuine
three-object groupoid.  Starting with a fresh arrow `s : Y ⟶ Z`, the
successive `U`, `S`, `U`, and `T` components return the difference-product
parameter `a e⁻¹ b`.-/
theorem groupoidFourArrowComposite (e a b : X ⟶ Y) (s : Y ⟶ Z) :
    (a ≫ s) ≫ inv (inv b ≫ e ≫ s) =
      groupoidDifferenceProduct e a b := by
  simp [groupoidDifferenceProduct, Category.assoc]

/-- The four-arrow groupoid construction computes multiplication in the
difference chart.-/
theorem groupoidFourArrowComposite_chart (e a b : X ⟶ Y) (s : Y ⟶ Z) :
    groupoidDifferenceChart e a * groupoidDifferenceChart e b =
      groupoidDifferenceChart e ((a ≫ s) ≫ inv (inv b ≫ e ≫ s)) := by
  rw [groupoidFourArrowComposite]
  exact groupoidDifferenceChart_mul e a b

/-- The arrow family `X ⟶ Y`, based at `e`, is equivalent to the vertex
group at `X`.-/
def groupoidDifferenceEquiv (e : X ⟶ Y) : (X ⟶ Y) ≃ (X ⟶ X) where
  toFun := groupoidDifferenceChart e
  invFun g := g ≫ e
  left_inv a := by simp [groupoidDifferenceChart, Category.assoc]
  right_inv g := by simp [groupoidDifferenceChart, Category.assoc]

/-- A genuine groupoid transports its vertex-group operations to a
rational group chunk on every nonempty arrow family.  Multiplication and
inverse are exactly the difference-product formulas used in blueprint
(8.3).-/
def groupoidArrowChunk (e : X ⟶ Y) : RationalGroupChunk (X ⟶ Y) where
  mul := groupoidDifferenceProduct e
  inv := groupoidDifferenceInverse e
  mul_assoc a b c := by
    simp [groupoidDifferenceProduct, Category.assoc]
  inv_mul_mul a b := by
    simp [groupoidDifferenceProduct, groupoidDifferenceInverse,
      Category.assoc]
  mul_mul_inv a b := by
    simp [groupoidDifferenceProduct, groupoidDifferenceInverse,
      Category.assoc]

/-- The groupoid difference chart intertwines the transported chunk
multiplication with multiplication in the vertex group.-/
theorem groupoidDifferenceEquiv_mul (e a b : X ⟶ Y) :
    groupoidDifferenceEquiv e ((groupoidArrowChunk e).mul a b) =
      groupoidDifferenceEquiv e a * groupoidDifferenceEquiv e b := by
  exact (groupoidDifferenceChart_mul e a b).symm

/-- The groupoid difference chart intertwines the transported chunk
inverse with inversion in the vertex group.-/
theorem groupoidDifferenceEquiv_inv (e a : X ⟶ Y) :
    groupoidDifferenceEquiv e ((groupoidArrowChunk e).inv a) =
      (groupoidDifferenceEquiv e a)⁻¹ := by
  exact (groupoidDifferenceChart_inv e a).symm

end GroupoidDifferenceChart

section DifferenceChart

variable {G : Type*} [Group G]

/-- The difference chart based at `e`, sending a family member `a` to
the endomorphism `e⁻¹a`.-/
def differenceChart (e a : G) : G := e⁻¹ * a

/-- The family parameter representing the product of two elements in the
difference chart.-/
def differenceProduct (e a b : G) : G := a * e⁻¹ * b

/-- Multiplication in the difference chart is represented by
`a e⁻¹ b`, exactly as in blueprint (8.4).-/
theorem differenceChart_mul (e a b : G) :
    differenceChart e a * differenceChart e b =
      differenceChart e (differenceProduct e a b) := by
  simp [differenceChart, differenceProduct, mul_assoc]

/-- The family parameter representing the inverse of `e⁻¹a`.-/
def differenceInverse (e a : G) : G := e * a⁻¹ * e

/-- Inversion is closed in the difference chart, represented by
`e a⁻¹ e`.-/
theorem differenceChart_inv (e a : G) :
    (differenceChart e a)⁻¹ = differenceChart e (differenceInverse e a) := by
  simp [differenceChart, differenceInverse, mul_assoc]

/-- The explicit cancellation calculation in the three-object
correspondence groupoid.  With
`u = se`, `sₐ = ua⁻¹`, `u_b = sb`, and `c = sₐ⁻¹u_b`, the output is
`c = ae⁻¹b`.-/
theorem groupoidComposite_eq (s e a b : G) :
    (((s * e) * a⁻¹)⁻¹) * (s * b) = differenceProduct e a b := by
  simp [differenceProduct, mul_assoc]

/-- The parameter formula from the groupoid cancellation agrees with
multiplication in the difference chart.-/
theorem groupoidComposite_chart (s e a b : G) :
    differenceChart e a * differenceChart e b =
      differenceChart e ((((s * e) * a⁻¹)⁻¹) * (s * b)) := by
  rw [groupoidComposite_eq]
  exact differenceChart_mul e a b

end DifferenceChart

section SixPointPattern

variable {G : Type*} [Group G]

/-- The normalized six-point group configuration of blueprint (8.3), in
the order `(S, T, U, S', T', U')`.-/
def sixPointGroupTuple (α γ ε : G) : Fin 6 → G :=
  ![α, γ, α * γ, ε, α * γ * ε, γ * ε]

@[simp] theorem sixPointGroupTuple_zero (α γ ε : G) :
    sixPointGroupTuple α γ ε 0 = α := rfl

@[simp] theorem sixPointGroupTuple_one (α γ ε : G) :
    sixPointGroupTuple α γ ε 1 = γ := rfl

@[simp] theorem sixPointGroupTuple_two (α γ ε : G) :
    sixPointGroupTuple α γ ε 2 = α * γ := rfl

@[simp] theorem sixPointGroupTuple_three (α γ ε : G) :
    sixPointGroupTuple α γ ε 3 = ε := rfl

@[simp] theorem sixPointGroupTuple_four (α γ ε : G) :
    sixPointGroupTuple α γ ε 4 = α * γ * ε := rfl

@[simp] theorem sixPointGroupTuple_five (α γ ε : G) :
    sixPointGroupTuple α γ ε 5 = γ * ε := rfl

/-- The four product identities corresponding to the four dependent
triples of a partial quadrangle.-/
theorem sixPointGroupTuple_relations (α γ ε : G) :
    sixPointGroupTuple α γ ε 2 =
        sixPointGroupTuple α γ ε 0 * sixPointGroupTuple α γ ε 1 ∧
    sixPointGroupTuple α γ ε 4 =
        sixPointGroupTuple α γ ε 0 * sixPointGroupTuple α γ ε 5 ∧
    sixPointGroupTuple α γ ε 5 =
        sixPointGroupTuple α γ ε 1 * sixPointGroupTuple α γ ε 3 ∧
    sixPointGroupTuple α γ ε 4 =
        sixPointGroupTuple α γ ε 2 * sixPointGroupTuple α γ ε 3 := by
  simp [mul_assoc]

end SixPointPattern

end

end AclGeom
