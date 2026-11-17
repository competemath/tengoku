import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRepAdic_detIsCyclotomic_baseChangeAlong

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/--
@isnad1 id=detiscyc.2h5v.s6.3c40fbb80c46 from=translated src=- shape=cbde18a5 vocab=26b7bab2
-/
theorem Tengoku.FltAnthropic.GaloisRepAdic.detIsCyclotomic_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.DetIsCyclotomic p) : (ρ.baseChangeAlong φ hφ).DetIsCyclotomic p := by exact @_root_.P2MW.S_GaloisRepAdic_detIsCyclotomic_baseChangeAlong.solution A B _ _ _ _ φ hφ ρ p h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
