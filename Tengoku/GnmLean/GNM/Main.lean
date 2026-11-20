import Tengoku.GnmLean.GNM.Assembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The classification

The three statements of the assembly are mutually exclusive and cover every interval, so each of
them can be read as an equivalence: the count is one exactly on the first exceptional set, two
exactly on the second, and at least three everywhere else. The family of intervals six below a power
of three is one of the families of the second set, so each of its members has exactly two good
partitions.
-/

namespace GNM

open GN

noncomputable section

/-- The count is one exactly on the first exceptional set.
@isnad1 id=iff.1h1v.s4.133de16b9cc0 from=translated src=- shape=cd71a022 vocab=ad541d30
-/
theorem count_eq_one_iff_internal (n : ℕ) (hn : 1 ≤ n) : count n = 1 ↔ Nu n := by
  constructor
  · intro h
    by_contra hnu
    by_cases he : E2 n
    · rw [count_eq_two_of_e2 he] at h
      omega
    · have h3 := three_le_count_of_not_exceptional n hn hnu he
      omega
  · exact fun h => count_eq_one_of_nu h

/-- The count is two exactly on the second exceptional set.
@isnad1 id=iff.0h1v.s3.3bdfe4e8ec8b from=translated src=- shape=f72d1292 vocab=4bf95cf5
-/
theorem count_eq_two_iff_internal (n : ℕ) : count n = 2 ↔ E2 n := by
  constructor
  · intro h
    by_contra he
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [count_zero] at h
      omega
    · by_cases hnu : Nu n
      · rw [count_eq_one_of_nu hnu] at h
        omega
      · have h3 := three_le_count_of_not_exceptional n (by omega) hnu he
        omega
  · exact fun h => count_eq_two_of_e2 h

/-- The count is at least three exactly outside the two exceptional sets.
@isnad1 id=iff.1h1v.s4.26284d2a3fe9 from=translated src=- shape=4acb5dec vocab=f2a070b5
-/
theorem three_le_count_iff_internal (n : ℕ) (hn : 1 ≤ n) : 3 ≤ count n ↔ ¬ Nu n ∧ ¬ E2 n := by
  constructor
  · intro h
    refine ⟨fun hnu => ?_, fun he => ?_⟩
    · rw [count_eq_one_of_nu hnu] at h
      omega
    · rw [count_eq_two_of_e2 he] at h
      omega
  · exact fun h => three_le_count_of_not_exceptional n hn h.1 h.2

/-- Each interval six below a power of three has exactly two good partitions.
@isnad1 id=eq.2h2v.s5.9afc5306bc05 from=translated src=- shape=2e582100 vocab=110fc0bd
-/
theorem count_eq_two_of_add_six_internal (n t : ℕ) (ht : 3 ≤ t) (h : n + 6 = 3 ^ t) :
    count n = 2 :=
  count_eq_two_of_e2 (Or.inr (Or.inr ⟨t, ht, h⟩))

end

end GNM
