import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_map_intCast_pow_char_eq_qExpand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_map_intCast_pow_char_eq_qExpand.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve
theorem ModularCurve.map_intCast_pow_char_eq_qExpand {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (s : LaurentSeries ℤ) :
    (s.map (Int.castRingHom K)) ^ ℓ = qExpand K ℓ (s.map (Int.castRingHom K)) := by exact @_root_.P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.solution K _ ℓ _ _ s
