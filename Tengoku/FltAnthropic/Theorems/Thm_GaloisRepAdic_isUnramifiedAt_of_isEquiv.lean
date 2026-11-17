import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRepAdic_isUnramifiedAt_of_isEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRepAdic_isUnramifiedAt_of_isEquiv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/--
@isnad1 id=isunrami.2h4v.s5.4328d4ba96f4 from=translated src=- shape=fadfb841 vocab=2fb060c9
-/
theorem Tengoku.FltAnthropic.GaloisRepAdic.isUnramifiedAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by exact @_root_.P2MW.S_GaloisRepAdic_isUnramifiedAt_of_isEquiv.solution A _ _ ρ₁ ρ₂ e q h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
