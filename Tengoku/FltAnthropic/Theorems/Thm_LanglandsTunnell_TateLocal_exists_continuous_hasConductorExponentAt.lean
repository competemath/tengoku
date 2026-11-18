import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

/--
@isnad1 id=ex.1h3v.s11.fd3069c7fffb from=translated src=- shape=892ebd2d vocab=cdade096
-/
theorem LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ) (hc : 2 ≤ c) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c := by exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt.solution K _ _ v c hc
