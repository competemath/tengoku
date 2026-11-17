import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SolRigidityBase

/--
@isnad1 id=eq.2h3v.s9.49526f16752f from=translated src=- shape=cee02048 vocab=6891efb9
-/
theorem appLE_self_eq_id_of_eq_id {B : Scheme.{u}} (q : B ⟶ B) (hq : q = 𝟙 B) (U : B.Opens)
    (e : U ≤ q ⁻¹ᵁ U) : q.appLE U U e = 𝟙 _ := by
  subst hq
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact B.presheaf.map_id _

/--
@isnad1 id=eq.4h6v.s11.a3aad98366e8 from=translated src=- shape=ada1b1de vocab=45c0b6f5
-/
theorem main
    {X B Y : Scheme.{u}} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
    (hp : IsClosedMap p)
    (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
    (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
    p ≫ ε ≫ f = f := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_

  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial

  have hC : IsClosed (p '' ((f ⁻¹ᵁ V : Set X)ᶜ)) :=
    hp _ (f ⁻¹ᵁ V).isOpen.isClosed_compl
  have hbC : p x ∈ (⟨(p '' ((f ⁻¹ᵁ V : Set X)ᶜ))ᶜ, hC.isOpen_compl⟩ : B.Opens) := by
    rintro ⟨x', hx', e⟩
    apply hx'
    change f x' ∈ V
    rw [← hf x', e, hf x]
    exact hxV

  obtain ⟨U, hU, hbU, hUC⟩ := exists_isAffineOpen_mem_and_subset hbC
  have e₁ : p ⁻¹ᵁ U ≤ f ⁻¹ᵁ V := by
    intro x' hx'
    by_contra h
    exact hUC hx' ⟨x', h, rfl⟩
  have e₂ : p ⁻¹ᵁ U ≤ (p ≫ ε ≫ f) ⁻¹ᵁ V := by
    intro x' hx'
    change (p ≫ ε ≫ f) x' ∈ V
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hf]
    exact e₁ hx'
  refine ⟨p ⁻¹ᵁ U, hbU, ?_⟩

  rw [← Scheme.Hom.resLE_comp_ι _ e₂, ← Scheme.Hom.resLE_comp_ι _ e₁]
  congr 1
  haveI : IsAffine V := hV
  apply ext_of_isAffine
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  congr 2

  have e₄ : U ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    intro b hb
    change p (ε b) ∈ U
    rwa [← Scheme.Hom.comp_apply, hε]
  have key : p.app U ≫ ε.appLE (p ⁻¹ᵁ U) U e₄ = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_self_eq_id_of_eq_id _ hε _ _

  have dec : (p ≫ ε ≫ f).appLE V (p ⁻¹ᵁ U) e₂ =
      f.appLE V (p ⁻¹ᵁ U) e₁ ≫ ε.appLE (p ⁻¹ᵁ U) U e₄ ≫ p.app U := by
    rw [Scheme.Hom.app_eq_appLE p, Scheme.Hom.appLE_comp_appLE_assoc ε f,
      Scheme.Hom.appLE_comp_appLE p (ε ≫ f)]
  rw [dec]

  set θ := ε.appLE (p ⁻¹ᵁ U) U e₄ ≫ p.app U with hθ
  have hθid : θ = 𝟙 _ := by
    ext t
    obtain ⟨r, rfl⟩ := hH0 U hU t
    change (p.app U ≫ θ) r = p.app U r
    rw [hθ, reassoc_of% key]
  rw [hθid, Category.comp_id]

end SolRigidityBase

/--
@isnad1 id=eq.4h6v.s11.a3aad98366e8 from=translated src=- shape=ada1b1de vocab=45c0b6f5
-/
theorem solution
    {X B Y : Scheme.{u}} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
    (hp : IsClosedMap p)
    (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
    (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
    p ≫ ε ≫ f = f :=
  SolRigidityBase.main p ε hε hp hH0 f hf
