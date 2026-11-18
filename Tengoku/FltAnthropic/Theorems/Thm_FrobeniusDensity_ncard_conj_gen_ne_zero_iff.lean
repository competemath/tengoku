import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Data.Set.Card
import Tengoku.FltAnthropic.P2M.Sol.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem FrobeniusDensity.ncard_conj_gen_ne_zero_iff {G : Type*} [Group G] [Finite G]
    (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by exact @_root_.P2MW.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.solution G _ _ σ τ
