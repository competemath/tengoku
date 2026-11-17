import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=ex.5h7v.s14.5a20233a6eee from=translated src=- shape=c29a0c7d vocab=43483f94
-/
theorem AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (m : ℕ)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) (e : V ≤ f ⁻¹ᵁ U)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
    ∃ (U' : (Spec (Y.residueField (f.base x))).Opens) (V' : (f.fiber (f.base x)).Opens) (_ : IsAffineOpen V')
      (_ : f.asFiber x ∈ V') (e' : V' ≤ (f.fiberToSpecResidueField (f.base x)) ⁻¹ᵁ U'),
      ((f.fiberToSpecResidueField (f.base x)).appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension m := by exact @_root_.P2MW.S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField.solution X Y f x m U hU V hV hxV e h
