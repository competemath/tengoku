import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded compositions

This file provides the bounded allocation lemma used by the shelf construction.
-/

open scoped BigOperators

namespace BurningPath

/--
If `m` slots each have capacity `a`, every total `s ≤ m * a` can be distributed
among the slots without exceeding their capacities.-/
theorem exists_fin_bounded_composition (m a s : ℕ) (h : s ≤ m * a) :
    ∃ e : Fin m → ℕ, (∀ i, e i ≤ a) ∧ ∑ i, e i = s := by
  induction m generalizing s with
  | zero =>
      have hs : s = 0 := by simpa using h
      subst s
      exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, by simp⟩
  | succ m ih =>
      let x := min s a
      have hx_le_a : x ≤ a := min_le_right s a
      have hx_le_s : x ≤ s := min_le_left s a
      have htail : s - x ≤ m * a := by
        by_cases hsa : s ≤ a
        · simp [x, min_eq_left hsa]
        · have has : a ≤ s := Nat.le_of_not_ge hsa
          simp only [Nat.succ_mul] at h
          simp only [x, min_eq_right has]
          omega
      obtain ⟨e, he_bound, he_sum⟩ := ih (s - x) htail
      refine ⟨Fin.cons x e, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa using hx_le_a
        · simpa using he_bound j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, he_sum]
        omega

end BurningPath
