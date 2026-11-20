/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEDominantVectors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem rankSum_eq_three_counts {ts : List ADEType}
    (htypes : ∀ t ∈ ts, t = .A 11 ∨ t = .D 7 ∨ t = .E6) :
    ADEType.rankSum ts =
      11 * ts.count (.A 11) + 7 * ts.count (.D 7) + 6 * ts.count .E6 := by
  induction ts with
  | nil => simp [ADEType.rankSum]
  | cons t ts ih =>
      have htail : ∀ s ∈ ts, s = .A 11 ∨ s = .D 7 ∨ s = .E6 :=
        fun s hs => htypes s (List.mem_cons_of_mem t hs)
      have hi := ih htail
      rcases htypes t (by simp) with rfl | rfl | rfl <;>
        simp [ADEType.rankSum_cons, ADEType.rank] <;> omega

theorem ade_rank24_height_eleven_layouts {ts : List ADEType}
    (hrank : ADEType.rankSum ts = 24)
    (htypes : ∀ t ∈ ts, t = .A 11 ∨ t = .D 7 ∨ t = .E6) :
    ts.Perm [.E6, .E6, .E6, .E6] ∨ ts.Perm [.A 11, .D 7, .E6] := by
  have hc := rankSum_eq_three_counts htypes
  have hcases :
      (ts.count (.A 11) = 0 ∧ ts.count (.D 7) = 0 ∧ ts.count .E6 = 4) ∨
      (ts.count (.A 11) = 1 ∧ ts.count (.D 7) = 1 ∧ ts.count .E6 = 1) := by
    have ha : ts.count (.A 11) ≤ 2 := by omega
    have hb : ts.count (.D 7) ≤ 3 := by omega
    have hdiv : (6 : ℤ) ∣ (ts.count (.A 11) : ℤ) - ts.count (.D 7) := by
      refine ⟨2 * (ts.count (.A 11) : ℤ) + ts.count (.D 7) + ts.count .E6 - 4, ?_⟩
      omega
    obtain ⟨k, hk⟩ := hdiv
    have hk0 : k = 0 := by omega
    omega
  rcases hcases with ⟨ha, hd, he⟩ | ⟨ha, hd, he⟩
  · left
    apply List.perm_iff_count.mpr
    intro t
    by_cases hA : t = .A 11
    · subst t; simpa using ha
    by_cases hD : t = .D 7
    · subst t; simpa using hd
    by_cases hE : t = .E6
    · subst t; simpa using he
    have hnot : t ∉ ts := by
      intro ht
      rcases htypes t ht with h | h | h <;> contradiction
    rw [List.count_eq_zero.mpr hnot]
    symm
    apply List.count_eq_zero.mpr
    simpa using hE
  · right
    apply List.perm_iff_count.mpr
    intro t
    by_cases hA : t = .A 11
    · subst t; simpa using ha
    by_cases hD : t = .D 7
    · subst t; simpa using hd
    by_cases hE : t = .E6
    · subst t; simpa using he
    have hnot : t ∉ ts := by
      intro ht
      rcases htypes t ht with h | h | h <;> contradiction
    rw [List.count_eq_zero.mpr hnot]
    symm
    apply List.count_eq_zero.mpr
    simpa using not_or.mpr ⟨hA, not_or.mpr ⟨hD, hE⟩⟩

end SRG266.Lattice
