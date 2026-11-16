import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isfinite.0h5v.s5.37875898305c from=translated src=- shape=bbf54670 vocab=16112a3f
-/
theorem solution
    {X₀ X Y : Scheme.{u}} (i : X₀ ⟶ X) [Surjective i] (g : X ⟶ Y) [IsProper g] [IsFinite (i ≫ g)] :
    IsFinite g := by
  have hq : LocallyQuasiFinite g := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton g fun y => ?_
    have hfin : ((i ≫ g) ⁻¹' {y}).Finite := (i ≫ g).finite_preimage_singleton y
    refine (hfin.image i).subset ?_
    intro x hx
    obtain ⟨x₀, rfl⟩ := ‹Surjective i›.surj x
    exact ⟨x₀, by simpa [Scheme.Hom.comp_base] using hx, rfl⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g
