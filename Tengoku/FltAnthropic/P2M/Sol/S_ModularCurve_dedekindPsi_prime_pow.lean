import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.Seed.Data.Nat.Squarefree
import Tengoku.Seed.NumberTheory.Divisors
import Tengoku.Seed.Tactic.IntervalCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_dedekindPsi_prime_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_dedekindPsi_prime_pow

open _root_.ModularCurve open _root_.Finset open _root_.Nat open _root_.Finset.Nat

theorem solution (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hsqfree : ∀ j, Squarefree (p ^ j) ↔ j ≤ 1 := fun j => by
    constructor
    · intro hsq
      by_contra hj
      exact hp.one_lt.ne'
        (Nat.isUnit_iff.mp (hsq p (by rw [← pow_two]; exact pow_dvd_pow p (by omega))))
    · intro hj
      interval_cases j
      · simp
      · simpa using hp.prime.squarefree
  have hfilter : {d ∈ (p ^ k).divisors | Squarefree d} = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hsq⟩
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have : j ≤ 1 := (hsqfree j).mp hsq
      interval_cases j
      · exact Or.inl (pow_zero p)
      · exact Or.inr (pow_one p)
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, pow_ne_zero _ hp.pos.ne'⟩, squarefree_one⟩
      · exact ⟨⟨dvd_pow_self _ hk, pow_ne_zero _ hp.pos.ne'⟩, hp.prime.squarefree⟩
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  rw [dedekindPsi, hfilter, Finset.sum_pair hp.one_lt.ne, Nat.div_one, hdiv]
