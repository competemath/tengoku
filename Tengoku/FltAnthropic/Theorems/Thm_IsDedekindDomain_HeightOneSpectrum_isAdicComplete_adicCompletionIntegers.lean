import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
universe u v
open IsDedekindDomain
theorem IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by exact @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers.solution R _ _ K _ _ _ v
