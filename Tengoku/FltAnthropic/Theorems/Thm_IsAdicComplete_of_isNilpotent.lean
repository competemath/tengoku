import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsAdicComplete_of_isNilpotent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsAdicComplete_of_isNilpotent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing
/--
@isnad1 id=isadicco.1h2v.s6.b0847a08ba76 from=translated src=- shape=dc8fba2f vocab=83598597
-/
theorem IsAdicComplete.of_isNilpotent {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R := by exact @_root_.P2MW.S_IsAdicComplete_of_isNilpotent.solution R _ I hI
