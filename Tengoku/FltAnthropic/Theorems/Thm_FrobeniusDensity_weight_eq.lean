import Tengoku.Seed.NumberTheory.ArithmeticFunction.Moebius
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Data.Set.Card
import Tengoku.FltAnthropic.P2M.Sol.S_FrobeniusDensity_weight_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FrobeniusDensity_weight_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Classical in
theorem FrobeniusDensity.weight_eq {G : Type*} [Group G] [Finite G] (σ τ : G) :
    ∑ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
          ((f : ℤ) * ({x : G ⧸ Subgroup.zpowers (σ ^ (orderOf σ / f)) | τ • x = x}.ncard : ℤ))
      = ({g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard : ℤ) := by exact @_root_.P2MW.S_FrobeniusDensity_weight_eq.solution G _ _ σ τ
