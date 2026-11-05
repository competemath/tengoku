/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.Grp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Group structure on a subobject with restricted operations

The named consumer is the reduced closed algebraic subgroup in blueprint `lem:curve-coset`.
The unit, multiplication and inverse are actual morphisms into the subobject; their
factorization identities through a monomorphism imply all group-object laws.

**Status:** proved; used by `exists_connectedClosedSubgroup_of_points`.
-/

namespace AclGeom

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Restricted unit, multiplication and inverse make a monic subobject into a group object.
Named consumer: the reduced closed subgroup in the general curve-coset theorem.-/
@[instance_reducible]
noncomputable def groupObjectOfMono {H G : C} [GrpObj G] (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (j : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G]) (hj : j ≫ i = i ≫ ι[G]) :
    GrpObj H := by
  have hmul {T : C} (p : T ⟶ H ⊗ H) :
      p ≫ m ≫ i = (p ≫ fst H H ≫ i) * (p ≫ snd H H ≫ i) := by
    have hp : p ≫ (i ⊗ₘ i) = lift (p ≫ fst H H ≫ i) (p ≫ snd H H ≫ i) := by
      apply hom_ext <;> simp [Category.assoc]
    calc
      p ≫ m ≫ i = (p ≫ (i ⊗ₘ i)) ≫ μ[G] := by rw [hm, Category.assoc]
      _ = (p ≫ fst H H ≫ i) * (p ≫ snd H H ≫ i) := congrArg (fun t ↦ t ≫ μ[G]) hp
  refine
    { one := e, mul := m, inv := j
      one_mul := ?_, mul_one := ?_, mul_assoc := ?_, left_inv := ?_, right_inv := ?_ }
  · apply (cancel_epi (λ_ H).inv).1
    apply (cancel_mono i).1
    simp [Category.assoc, hmul, he, MonObj.comp_mul]
    rfl
  · apply (cancel_epi (ρ_ H).inv).1
    apply (cancel_mono i).1
    simp [Category.assoc, hmul, he, MonObj.comp_mul]
    rfl
  · apply (cancel_mono i).1
    simp [Category.assoc, hmul, MonObj.comp_mul, _root_.mul_assoc]
  · apply (cancel_mono i).1
    simp [Category.assoc, hm, he, hj]
  · apply (cancel_mono i).1
    simp [Category.assoc, hm, he, hj]

end AclGeom
