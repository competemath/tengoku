import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/--
@isnad1 id=eq.1h2v.s10.a8d417a6767d from=translated src=- shape=86d22dcf vocab=fe12068d
-/
theorem Tengoku.FltAnthropic.GaloisRepAdic.span_range_eq_top_of_residual_isAbsolutelyIrreducible
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (h : ρ.residual.IsAbsolutelyIrreducible) :
    Submodule.span A (Set.range ⇑ρ.ρ) = ⊤ := by exact @_root_.P2MW.S_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible.solution A _ _ ρ h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
