import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SiegelFunction
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_SiegelUnit_siegelFun_add_level

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_SiegelUnit_siegelFun_add_level.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ModularCurve

/--
@isnad1 id=and.0h3v.s7.f35b595dcaa8 from=translated src=- shape=8d28570f vocab=ca4c1968
-/
theorem ModularCurve.SiegelUnit.siegelFun_add_level (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by exact @_root_.P2MW.S_ModularCurve_SiegelUnit_siegelFun_add_level.solution N r s
