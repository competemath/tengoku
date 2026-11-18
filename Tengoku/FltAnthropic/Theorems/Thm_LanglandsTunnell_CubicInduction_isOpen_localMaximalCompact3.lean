import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsDedekindDomain

/--
@isnad1 id=isopen.0h3v.s9.bd261fba8aef from=translated src=- shape=6f37c14c vocab=e6eea353
-/
theorem
LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsOpen ((localMaximalCompact3 R K v : Subgroup (GL (Fin 3) (v.adicCompletion K))) :
      Set (GL (Fin 3) (v.adicCompletion K))) := by exact @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3.solution R K _ _ _ _ _ v
