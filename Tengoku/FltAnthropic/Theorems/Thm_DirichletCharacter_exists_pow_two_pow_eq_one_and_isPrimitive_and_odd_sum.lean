import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.1h1v.s9.6234a1fcaf93 from=translated src=- shape=12b19da9 vocab=b21d325e
-/
theorem DirichletCharacter.exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    ∃ (n : ℕ) (χ : DirichletCharacter ℂ ℓ), 0 < n ∧
      (∀ j : ℕ, (χ ^ (2 * j + 1)).IsPrimitive ∧ (χ ^ (2 * j + 1)).Odd) ∧
      (∀ d : ZMod ℓ, χ d ^ (2 * n) = 1 ∨ χ d = 0) ∧
      _root_.Odd (∑ a ∈ Finset.range ℓ,
        (a : ℤ) * (if χ (a : ZMod ℓ) = 1 then 1 else if χ (a : ZMod ℓ) = -1 then -1 else 0)) := by exact @_root_.P2MW.S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum.solution ℓ _ hℓ
