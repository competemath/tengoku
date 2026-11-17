import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=eq.2h7v.s8.308dc62a5688 from=translated src=- shape=ec5e7394 vocab=d06d75a7
-/
theorem solution
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f]
    {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (s₁ s₂ : Spec (CommRingCat.of ↥A) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom A.subtype) ≫ s₁ = Spec.map (CommRingCat.ofHom A.subtype) ≫ s₂)
    (hf : s₁ ≫ f = s₂ ≫ f) : s₁ = s₂ := by
  have hA : CommRingCat.ofHom A.subtype = CommRingCat.ofHom (algebraMap (↥A) Ω) := rfl
  let S : ValuativeCommSq f :=
    { R := ↥A
      K := Ω
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap (↥A) Ω)) ≫ s₁
      i₂ := s₁ ≫ f
      commSq := ⟨by rw [Category.assoc]⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  let l₁ : S.commSq.LiftStruct := ⟨s₁, rfl, rfl⟩
  let l₂ : S.commSq.LiftStruct := ⟨s₂, by rw [← hA]; exact h.symm, hf.symm⟩
  have := hsub.elim l₁ l₂
  exact congrArg CommSq.LiftStruct.l this
