/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.Normal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transporting an actual normal conjugation diagram

**Status:** a commuting group factorization transports the actual joint conjugation
diagram in every cartesian monoidal category. Named consumer: the finite-coordinate
conjugation character of the actual normal subgroup in the regular-affine model (#21).
-/

namespace AclGeom.NormalCoordinateConjugation
noncomputable section
open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj CategoryTheory.GrpObj

/-- A commuting group factorization transports the actual conjugation diagram.
Named consumer: finite-coordinate conjugation of the actual normal subgroup.
@isnad1 id=eq.2h10v.s8.b4ee197ef33b from=translated src=- shape=2adfe6b0 vocab=20c8b43a
-/
theorem factor_conjugation
    {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G H N M : C} [GrpObj G] [GrpObj H]
    (i : N ⟶ G) (j : M ⟶ H) (f : G ⟶ H) [IsMonHom f]
    (β : N ⟶ M) (ψ : G ⊗ N ⟶ N)
    (hfactor : β ≫ j = i ≫ f) (hψ : ψ ≫ i = G ◁ i ≫ conj G) :
    (ψ ≫ β) ≫ j = (f ⊗ₘ β) ≫ H ◁ j ≫ conj H := by
  have hconj : conj G ≫ f = (f ⊗ₘ f) ≫ conj H := by
    change (fst G G * snd G G * (fst G G)⁻¹) ≫ f =
      (f ⊗ₘ f) ≫ (fst H H * snd H H * (fst H H)⁻¹)
    simp only [mul_comp, inv_comp, comp_mul, comp_inv, tensorHom_fst, tensorHom_snd]
  have hsq : G ◁ i ≫ (f ⊗ₘ f) = (f ⊗ₘ β) ≫ H ◁ j := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, whiskerLeft_fst_assoc, whiskerLeft_fst]
    · simp only [Category.assoc, tensorHom_snd, whiskerLeft_snd_assoc, whiskerLeft_snd,
        tensorHom_snd_assoc, hfactor]
  calc
    _ = (ψ ≫ i) ≫ f := by rw [Category.assoc, hfactor, ← Category.assoc]
    _ = (G ◁ i ≫ conj G) ≫ f := by rw [hψ]
    _ = (G ◁ i ≫ (f ⊗ₘ f)) ≫ conj H := by
      rw [Category.assoc, hconj, ← Category.assoc]
    _ = _ := by rw [hsq, Category.assoc]

end
end AclGeom.NormalCoordinateConjugation
