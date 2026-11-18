import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.5h10v.s9.0f65d82c8b5d from=translated src=- shape=dc987bb0 vocab=72379b42
-/
theorem Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
    (q : ℕ) (hq : 1 < q) (P Q₁ Q₂ : Polynomial ℂ) (hQ₂ : Q₂ ≠ 0) (m k : ℤ) (γ Zd : ℂ → ℂ) (S S₁ : Set ℂ)
    (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s))
    (h₁ : ∀ s ∈ S₁,
      Zd s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) * γ s) :
    (∀ s : ℂ, (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ∧
    ∃ R : Finset ℝ, ∀ s ∈ S₁, (q : ℝ) ^ (-s.re) ∉ R →
      Zd s = γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s))) := by exact @_root_.P2MW.S_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite.solution q hq P Q₁ Q₂ hQ₂ m k γ Zd S S₁ hS h h₁
