import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Ideal.card_quotient_pow_hilbertSamuel_linear_of_moduleFinite
    (R : Type*) [CommRing R] [Module.Finite ℤ R]
    (I : Ideal R) (q : ℕ) [Fact q.Prime] (hqI : (q : R) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (R ⧸ I ^ m) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (R ⧸ I ^ m) * q ^ C := by exact @_root_.P2MW.S_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite.solution R _ _ I q _ hqI
