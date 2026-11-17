import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {F : Scheme.{u}} (g : F ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (hg : SmoothOfRelativeDimension n g)
    (m : ℕ) (U : (Spec (CommRingCat.of k)).Opens) (W : F.Opens) (hW : IsAffineOpen W)
    (w : F) (hw : w ∈ W) (e : W ≤ g ⁻¹ᵁ U)
    (hm : (g.appLE U W e).hom.IsStandardSmoothOfRelativeDimension m) : m = n := by exact @_root_.P2MW.S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension.solution k _ F g n hg m U W hW w hw e hm
