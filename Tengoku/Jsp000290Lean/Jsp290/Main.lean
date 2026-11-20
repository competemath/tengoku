import Tengoku.Jsp000290Lean.Jsp290.Positive
import Tengoku.Jsp000290Lean.Jsp290.Examples
import Tengoku.Jsp000290Lean.Jsp290.IntegerReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# JSP-000290 / Erdős problem 348: the full deletion-threshold classification

For nondecreasing integer sequences, deletion robustness at every set of `m`
occurrences and failure at every set of `n` occurrences (`m < n`) is possible
exactly when `m ≤ 1`. Completeness means representing all sufficiently large
integers. Equal-valued occurrences are not identified.

Mathematical source: Jesse Geneson, arXiv:2609.25107v1, Theorem 1.
-/

namespace Jsp290

theorem admissible_iff (m n : ℕ) (hmn : m < n) :
    Admissible m n ↔ m ≤ 1 := by
  constructor
  · rintro ⟨a, hm, hrobust, hfail⟩
    by_contra hn
    have hm2 : 2 ≤ m := by omega
    by_cases hu : ∀ C : ℤ, ∃ i : ℕ, C < a i
    · obtain ⟨b, hbm, hbp, htransfer⟩ := exists_positive_model a hm hu
      have hbmrobust : ∀ D : Finset ℕ, D.card = m → CompleteAfter b D := by
        intro D hD
        obtain ⟨E, hE, hiff⟩ := htransfer D
        exact hiff.mpr (hrobust E (hE.trans hD))
      have hbnfail : ∀ D : Finset ℕ, D.card = n → ¬ CompleteAfter b D := by
        intro D hD hc
        obtain ⟨E, hE, hiff⟩ := htransfer D
        exact hfail E (hE.trans hD) (hiff.mp hc)
      exact positive_exclusion hbm hbp hm2 hbmrobust hbnfail
    · have hb : ∃ B : ℤ, ∀ i, a i ≤ B := by
        push_neg at hu
        exact hu
      have hc : Complete a :=
        (completeAfter_of_smaller_card hrobust ∅ (by simp)).complete
      obtain ⟨D, hD, hcD⟩ := exists_completeAfter_card_bounded hm hb hc n
      exact hfail D hD hcD
  · exact admissible_of_le_one m n hmn

/-- The complete target with its definitions expanded for statement review.-/
theorem jsp_000290 (m n : ℕ) (hmn : m < n) :
    (∃ a : ℕ → ℤ, Monotone a ∧
      (∀ D : Finset ℕ, D.card = m →
        ∃ T : ℤ, ∀ x : ℤ, T ≤ x →
          ∃ s : Finset ℕ, Disjoint s D ∧ ∑ i ∈ s, a i = x) ∧
      (∀ D : Finset ℕ, D.card = n →
        ¬ (∃ T : ℤ, ∀ x : ℤ, T ≤ x →
          ∃ s : Finset ℕ, Disjoint s D ∧ ∑ i ∈ s, a i = x))) ↔ m ≤ 1 :=
  admissible_iff m n hmn

end Jsp290
