import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isaffine.1h3v.s6.c30d42d676eb from=translated src=- shape=74b855d9 vocab=129e28ad
-/
theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [IsAffine X₀]
    (h : i.ker * i.ker = ⊥) : IsAffine X := by exact @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot.solution X₀ X i _ _ h
