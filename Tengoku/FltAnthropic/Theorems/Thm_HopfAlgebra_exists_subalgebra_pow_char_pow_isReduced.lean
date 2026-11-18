import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    ∃ (r : ℕ) (K' : Subalgebra k H), K' ≤ K ∧ K'.FG ∧ IsReduced ↥K' ∧
      (K' : Set H) = {y : H | ∃ x ∈ K, y = x ^ p ^ r} ∧
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') := by exact @_root_.P2MW.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.solution k _ _ p _ _ H _ _ K hΔ hS hfg
