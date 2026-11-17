import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_isDomain_functionField_tensorProduct_of_isIntegral_pullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_functionField_mem_range_algebraMap_rat_of_isAlgebraic_of_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (M : ℕ) [NeZero M]
    (X : Scheme.{0}) [IsIntegral X] (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.Away ((M : ℕ) : ℤ))))
    (hC : IsIntegral (CategoryTheory.Limits.pullback πX sC)) :
    ∃ hchar : CharZero X.functionField, haveI := hchar;
      ∀ x : X.functionField, IsAlgebraic ℚ x → x ∈ Set.range (algebraMap ℚ X.functionField) := by
  obtain ⟨hchar, hdom⟩ := AlgebraicGeometry.isDomain_functionField_tensorProduct_of_isIntegral_pullback M X πX C sC hC
  refine ⟨hchar, ?_⟩
  intro x hx
  exact IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed X.functionField C hdom x hx
