import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_maximalIdeal_eq_of_le_sup_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open IsLocalRing

/--
@isnad1 id=eq.2h2v.s8.ded05fe380b2 from=translated src=- shape=ead75b59 vocab=95893b03
-/
theorem IsLocalRing.maximalIdeal_eq_of_le_sup_sq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Ideal R) (hN : N ≤ maximalIdeal R) (h : maximalIdeal R ≤ N ⊔ maximalIdeal R ^ 2) :
    maximalIdeal R = N := by exact @_root_.P2MW.S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq.solution R _ _ _ N hN h
