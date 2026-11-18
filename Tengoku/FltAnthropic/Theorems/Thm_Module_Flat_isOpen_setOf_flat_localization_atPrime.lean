import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Flat_isOpen_setOf_flat_localization_atPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Module.Flat.isOpen_setOf_flat_localization_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} := by exact @_root_.P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.solution A B _ _ _ _ _
