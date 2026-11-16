import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (B : Subalgebra A L) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B ∧
      ∀ J : Ideal B, J ≠ ⊥ → IsFiniteLength A (B ⧸ J) := by exact @_root_.P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.solution A K L _ _ _ _ _ _ _ _ _ _ _ _ B
