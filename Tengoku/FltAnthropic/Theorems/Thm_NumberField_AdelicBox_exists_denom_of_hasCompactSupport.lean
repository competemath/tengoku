import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicBox_exists_denom_of_hasCompactSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicBox_exists_denom_of_hasCompactSupport.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.AdelicBox IsDedekindDomain
/--
@isnad1 id=ex.1h2v.s8.f121e2c95328 from=translated src=- shape=2e232f16 vocab=ed15b3a6
-/
theorem NumberField.AdelicBox.exists_denom_of_hasCompactSupport
    {F : Type*} [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ κ : F, h (algebraMap F (FiniteAdeleRing (𝓞 F) F) κ) ≠ 0 →
      ∃ a : 𝓞 F, (d : F) * κ = a := by exact @_root_.P2MW.S_NumberField_AdelicBox_exists_denom_of_hasCompactSupport.solution F _ _ h hcs
