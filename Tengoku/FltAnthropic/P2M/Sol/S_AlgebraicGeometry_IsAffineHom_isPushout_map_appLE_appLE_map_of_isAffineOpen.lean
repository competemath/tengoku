import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace Ws23C4

/--
@isnad1 id=ispushou.3h5v.s11.334467bde3d2 from=translated src=- shape=9d72ebbb vocab=70ff853c
-/
theorem main
    {V W : Scheme.{u}} (γ : W ⟶ V) [IsAffineHom γ] {U U' : V.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    IsPushout (V.presheaf.map (homOfLE h).op) (γ.appLE U' (γ ⁻¹ᵁ U') le_rfl)
      (γ.appLE U (γ ⁻¹ᵁ U) le_rfl) (W.presheaf.map (homOfLE (γ.preimage_mono h)).op) := by
  have H : IsPullback γ (𝟙 W) (𝟙 V) γ := IsPullback.of_vert_isIso ⟨by simp⟩
  have hUST : γ ⁻¹ᵁ U' ≤ γ ⁻¹ᵁ U' := le_rfl
  have hUSX : U ≤ (𝟙 V) ⁻¹ᵁ U' := h
  have hUY : γ ⁻¹ᵁ U = γ ⁻¹ᵁ U ⊓ (𝟙 W) ⁻¹ᵁ (γ ⁻¹ᵁ U') :=
    (inf_eq_left.mpr (γ.preimage_mono h)).symm
  have key := (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hU' (hU'.preimage γ) hU)
  have e1 : (𝟙 V : V ⟶ V).appLE U' U hUSX = V.presheaf.map (homOfLE h).op := by
    dsimp only [Scheme.Hom.appLE]
    rw [Scheme.Hom.id_app]
    erw [Category.id_comp]
    try rfl
  have e2 : (𝟙 W : W ⟶ W).appLE (γ ⁻¹ᵁ U') (γ ⁻¹ᵁ U) (by rw [hUY]; exact inf_le_right) =
      W.presheaf.map (homOfLE (γ.preimage_mono h)).op := by
    dsimp only [Scheme.Hom.appLE]
    rw [Scheme.Hom.id_app]
    erw [Category.id_comp]
    try rfl
  rw [e1, e2] at key
  exact key

end Ws23C4

/--
@isnad1 id=ispushou.3h5v.s11.334467bde3d2 from=translated src=- shape=9d72ebbb vocab=70ff853c
-/
theorem solution
    {V W : Scheme.{u}} (γ : W ⟶ V) [IsAffineHom γ] {U U' : V.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    IsPushout (V.presheaf.map (homOfLE h).op) (γ.appLE U' (γ ⁻¹ᵁ U') le_rfl)
      (γ.appLE U (γ ⁻¹ᵁ U) le_rfl) (W.presheaf.map (homOfLE (γ.preimage_mono h)).op) := by
  exact Ws23C4.main γ hU hU' h
