import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (π : X ⟶ Y) (c : Y ⟶ X) [IsClosedImmersion c] (hcπ : c ≫ π = 𝟙 Y)
    (huniq : ∀ s : Y ⟶ X, IsClosedImmersion s → s ≫ π = 𝟙 Y → s = c)
    (φ : X ≅ X) (φ₀ : Y ≅ Y) (hπ : φ.hom ≫ π = π ≫ φ₀.hom) :
    c ≫ φ.hom = φ₀.hom ≫ c := by

  have hs : IsClosedImmersion (φ₀.inv ≫ c ≫ φ.hom) := inferInstance
  have hsec : (φ₀.inv ≫ c ≫ φ.hom) ≫ π = 𝟙 Y := by
    rw [Category.assoc, Category.assoc, hπ, ← Category.assoc c, hcπ, Category.id_comp, Iso.inv_hom_id]
  have key := huniq _ hs hsec

  calc c ≫ φ.hom = φ₀.hom ≫ (φ₀.inv ≫ c ≫ φ.hom) := by rw [Iso.hom_inv_id_assoc]
    _ = φ₀.hom ≫ c := by rw [key]

