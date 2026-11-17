import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_range_pullbackMap_id_id_eq_preimage_range.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_range_pullbackMap_id_id_eq_preimage_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=eq.2h8v.s9.f31d1644428a from=translated src=- shape=e41505b6 vocab=49ac8810
-/
theorem solution
    {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (i : T' ⟶ T)
    (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 S = i ≫ g) :
    Set.range (pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂).base =
      (pullback.snd f g).base ⁻¹' Set.range i.base := by
  have h := Scheme.Pullback.range_map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂
  have h1 : Set.range ((𝟙 X : X ⟶ X) : X → X) = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
  rw [h1, Set.preimage_univ, Set.univ_inter] at h
  exact h
