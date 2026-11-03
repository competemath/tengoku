import Tengoku.Seed.Data.Int.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A dimension function supported in degree one -/
set_option autoImplicit false
namespace MagnitudeConjecture

/-- Three degree ranges determine a dimension function supported on adjacent shifts.
@isnad1 id=eq.3h4v.s7.fb2ecc870215 from=translated src=- shape=eb427084 vocab=bc5545b5
-/
theorem degreeOne_function_formula (q : ℤ → ℤ → ℕ) (D : ℕ)
    (hone : ∀ t, q (t + 1) t = D)
    (hlow : ∀ s t, s ≤ t → q s t = 0)
    (hhigh : ∀ t (n : ℕ), 0 < n → q (t + n + 1) t = 0)
    (s t : ℤ) : q s t = if s = t + 1 then D else 0 := by
  by_cases h : s = t + 1
  · subst s
    simpa using hone t
  · rw [ite_eq_right h]
    by_cases hst : s ≤ t
    · exact hlow s t hst
    · obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, 0 < n ∧ s = t + n + 1 := by
        refine ⟨(s - t - 1).toNat, ?_, ?_⟩ <;> omega
      exact hhigh t n hn

end MagnitudeConjecture
