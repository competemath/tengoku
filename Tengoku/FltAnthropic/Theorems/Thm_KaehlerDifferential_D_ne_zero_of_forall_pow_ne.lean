import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem KaehlerDifferential.D_ne_zero_of_forall_pow_ne
    {k : Type u} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 := by exact @_root_.P2MW.S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.solution k _ p hp _ c hc
