import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow
    {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (m : ℕ)
    (hexp : ∀ x : G, p ^ m • x = 0)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p) :
    IsAddCyclic G ∧ Nat.card G ∣ p ^ m := by exact @_root_.P2MW.S_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow.solution G _ _ p hp m hexp hsocle
