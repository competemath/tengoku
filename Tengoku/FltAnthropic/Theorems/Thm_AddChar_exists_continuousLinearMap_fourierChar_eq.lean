import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_AddChar_exists_continuousLinearMap_fourierChar_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddChar_exists_continuousLinearMap_fourierChar_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped FourierTransform
/--
@isnad1 id=ex.1h2v.s8.e6547df13f29 from=translated src=- shape=7e7ae69f vocab=01c16826
-/
theorem AddChar.exists_continuousLinearMap_fourierChar_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by exact @_root_.P2MW.S_AddChar_exists_continuousLinearMap_fourierChar_eq.solution E _ _ χ hχ
