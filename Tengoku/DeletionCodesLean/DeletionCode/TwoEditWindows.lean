import Tengoku.Seed.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms avoids_later_of_not_avoids` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms candidate_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_clean_block_among_three` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_clean_block` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Two edit positions cannot obstruct all three length-k blocks with offsets
0, k+1, and 2(k+1). The same offset is used in both words. The intervals have
a one-position gap, and their right endpoints fit inside length 3k+2.
The argument also covers k = 0.
-/
namespace DeletionCode.TwoEditWindows

/-- A half-open block of length k lies wholly before or wholly after an edit
position. The strict inequality on the latter side skips the edit itself.-/
def Avoids (k start edit : ℕ) : Prop := start + k ≤ edit ∨ edit < start

/-- If an edit obstructs one block, every later disjoint block avoids it.
@isnad1 id=avoids.2h4v.s5.f48d14dd9b5b from=translated src=- shape=8ca170ee vocab=05c28615
-/
theorem avoids_later_of_not_avoids {k start next edit : ℕ}
    (hgap : start + k ≤ next) (hbad : ¬ Avoids k start edit) :
    Avoids k next edit := by
  unfold Avoids at *
  right
  omega

/-- The candidate offsets all fit, including the final block's right endpoint.
@isnad1 id=le.1h2v.s6.860f76db6e97 from=translated src=- shape=9064789d vocab=ebd7a482
-/
theorem candidate_bound {k s : ℕ}
    (hs : s = 0 ∨ s = k + 1 ∨ s = 2 * (k + 1)) : s + k ≤ 3 * k + 2 := by
  rcases hs with rfl | rfl | rfl <;> omega

/-- Three separated candidate blocks suffice for any two edit positions.
@isnad1 id=ex.0h5v.s7.41de94cbb193 from=translated src=- shape=e4a9e494 vocab=923b6325
-/
theorem exists_clean_block_among_three (k a b p q : ℕ) :
    ∃ s : ℕ, (s = 0 ∨ s = k + 1 ∨ s = 2 * (k + 1)) ∧
      s + k ≤ 3 * k + 2 ∧
      (a + s + k ≤ p ∨ p < a + s) ∧
      (b + s + k ≤ q ∨ q < b + s) := by
  by_cases ha0 : Avoids k a p
  · by_cases hb0 : Avoids k b q
    · refine ⟨0, Or.inl rfl, by omega, ?_, ?_⟩
      · simpa only [Avoids, Nat.add_zero] using ha0
      · simpa only [Avoids, Nat.add_zero] using hb0
    · have hb1 : Avoids k (b + (k + 1)) q :=
        avoids_later_of_not_avoids (by omega) hb0
      have hb2 : Avoids k (b + 2 * (k + 1)) q :=
        avoids_later_of_not_avoids (by omega) hb0
      by_cases ha1 : Avoids k (a + (k + 1)) p
      · exact ⟨k + 1, Or.inr (Or.inl rfl), by omega, ha1, hb1⟩
      · have ha2 : Avoids k (a + 2 * (k + 1)) p :=
          avoids_later_of_not_avoids (by omega) ha1
        exact ⟨2 * (k + 1), Or.inr (Or.inr rfl), by omega, ha2, hb2⟩
  · have ha1 : Avoids k (a + (k + 1)) p :=
      avoids_later_of_not_avoids (by omega) ha0
    have ha2 : Avoids k (a + 2 * (k + 1)) p :=
      avoids_later_of_not_avoids (by omega) ha0
    by_cases hb1 : Avoids k (b + (k + 1)) q
    · exact ⟨k + 1, Or.inr (Or.inl rfl), by omega, ha1, hb1⟩
    · have hb2 : Avoids k (b + 2 * (k + 1)) q :=
        avoids_later_of_not_avoids (by omega) hb1
      exact ⟨2 * (k + 1), Or.inr (Or.inr rfl), by omega, ha2, hb2⟩

/-- Arithmetic interface for a common unedited subwindow of two words.
@isnad1 id=ex.0h5v.s6.d97d6e3c4d0a from=translated src=- shape=2230d11a vocab=923b6325
-/
theorem exists_clean_block (k a b p q : ℕ) :
    ∃ s : ℕ, s + k ≤ 3 * k + 2 ∧
      (a + s + k ≤ p ∨ p < a + s) ∧
      (b + s + k ≤ q ∨ q < b + s) := by
  obtain ⟨s, _, hbound, ha, hb⟩ := exists_clean_block_among_three k a b p q
  exact ⟨s, hbound, ha, hb⟩

end DeletionCode.TwoEditWindows
