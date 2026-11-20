/-
OEIS A048248: the trace of every `n`-step walk is a valid list.
-/
import Tengoku.OeisLean.OeisLean.A048248.Defs
import Tengoku.Seed.Algebra.BigOperators.Group.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A048248.trace_valid` (it only prints; the queue checks the axioms of every declaration). -/

namespace A048248

namespace Fwd

/-- Position after the walk `w` started at `pos`.-/
def endPos : List Bool → ℤ → ℤ
  | [], pos => pos
  | true :: w, pos => endPos w (pos + 1)
  | false :: w, pos => endPos w (pos - 1)

/--
@isnad1 id=and.0h2v.s5.cbc8888ec270 from=translated src=- shape=ae903b40 vocab=87502b97
-/
theorem endPos_bounds (w : List Bool) :
    ∀ pos : ℤ, pos - w.length ≤ endPos w pos ∧ endPos w pos ≤ pos + w.length := by
  induction w with
  | nil => intro pos; simp [endPos]
  | cons b w ih =>
    intro pos
    cases b
    · have := ih (pos - 1)
      simp only [endPos, List.length_cons]
      omega
    · have := ih (pos + 1)
      simp only [endPos, List.length_cons]
      omega

/--
@isnad1 id=eq.0h3v.s7.1e2dcd32abac from=translated src=- shape=bb8d1fbf vocab=dd657107
-/
theorem indSum (n : ℕ) (p : ℤ) : ∀ m : ℕ,
    ((List.range m).map fun i : ℕ => if p = (i : ℤ) - n then 1 else 0).sum =
      if -(n : ℤ) ≤ p ∧ p < (m : ℤ) - n then 1 else 0 := by
  intro m
  induction m with
  | zero => rw [ite_eq_right (by omega)]; simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

/--
@isnad1 id=eq.2h3v.s6.260399e914df from=translated src=- shape=7d56128f vocab=e27b0c2d
-/
theorem sum_edge (n : ℕ) (w : List Bool) :
    ∀ pos : ℤ, -(n : ℤ) ≤ pos - w.length → pos + w.length ≤ n →
      ((List.range (2 * n)).map fun i : ℕ => edgeCount w pos ((i : ℤ) - n)).sum = w.length := by
  induction w with
  | nil => intro pos _ _; simp [edgeCount]
  | cons b w ih =>
    intro pos h1 h2
    simp only [List.length_cons] at h1 h2
    cases b
    · simp only [edgeCount, List.sum_map_add, List.length_cons]
      rw [indSum, ih (pos - 1) (by omega) (by omega), ite_eq_left (by omega)]
      omega
    · simp only [edgeCount, List.sum_map_add, List.length_cons]
      rw [indSum, ih (pos + 1) (by omega) (by omega), ite_eq_left (by omega)]
      omega

/--
@isnad1 id=eq.0h1v.s5.bb33d0c41c78 from=translated src=- shape=af926cd6 vocab=d72b3eab
-/
theorem sum_filter_pos (l : List ℕ) : (l.filter (0 < ·)).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : 0 < a
    · simp [h, ih]
    · have : a = 0 := by omega
      subst this
      simp [ih]

/--
@isnad1 id=iff.0h3v.s5.5185745dad7b from=translated src=- shape=543343f5 vocab=d52c67d9
-/
theorem odd_edge (w : List Bool) : ∀ pos j : ℤ,
    Odd (edgeCount w pos j) ↔
      (pos ≤ j ∧ j < endPos w pos) ∨ (endPos w pos ≤ j ∧ j < pos) := by
  induction w with
  | nil =>
    intro pos j
    simp only [edgeCount, endPos]
    constructor
    · intro h; simp at h
    · omega
  | cons b w ih =>
    intro pos j
    cases b
    · simp only [edgeCount, endPos]
      split_ifs with h
      · rw [Nat.add_comm, Nat.odd_add_one, ih]; omega
      · rw [Nat.zero_add, ih]; omega
    · simp only [edgeCount, endPos]
      split_ifs with h
      · rw [Nat.add_comm, Nat.odd_add_one, ih]; omega
      · rw [Nat.zero_add, ih]; omega

/--
@isnad1 id=eq.2h3v.s6.c499d0e1a6c3 from=translated src=- shape=277e90a2 vocab=1fdd56dc
-/
theorem range_split (N i₁ i₂ : ℕ) (h1 : i₁ ≤ i₂) (h2 : i₂ ≤ N) :
    List.range N =
      List.range' 0 i₁ ++ List.range' i₁ (i₂ - i₁) ++ List.range' i₂ (N - i₂) := by
  have h := List.range'_append_1 (s := 0) (m := i₁) (n := i₂ - i₁)
  have h' := List.range'_append_1 (s := 0) (m := i₂) (n := N - i₂)
  simp only [Nat.zero_add] at h h'
  rw [h, show i₁ + (i₂ - i₁) = i₂ by omega, h', List.range_eq_range',
    show i₂ + (N - i₂) = N by omega]

end Fwd

open Fwd in
/--
@isnad1 id=valid.1h2v.s4.246c8a46564a from=translated src=- shape=1b77c6f3 vocab=34cfdc46
-/
theorem trace_valid (n : ℕ) (w : List Bool) (hw : w.length = n) : Valid n (trace n w) := by
  have hb := endPos_bounds w 0
  rw [hw] at hb
  refine ⟨?_, ?_, ?_⟩
  · unfold trace
    rw [sum_filter_pos, sum_edge n w 0 (by rw [hw]; omega) (by rw [hw]; omega), hw]
  · intro x hx
    unfold trace at hx
    simpa using (List.mem_filter.1 hx).2
  · obtain ⟨i₁, i₂, h12, h2N, hodd⟩ : ∃ i₁ i₂ : ℕ, i₁ ≤ i₂ ∧ i₂ ≤ 2 * n ∧
        ∀ i : ℕ, (Odd (edgeCount w 0 ((i : ℤ) - n)) ↔ i₁ ≤ i ∧ i < i₂) := by
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ endPos w 0 + n by omega)
      rcases le_or_gt 0 (endPos w 0) with h | h
      · refine ⟨n, k, by omega, by omega, fun i => ?_⟩
        rw [odd_edge]; omega
      · refine ⟨k, n, by omega, by omega, fun i => ?_⟩
        rw [odd_edge]; omega
    refine ⟨((List.range' 0 i₁).map fun i : ℕ => edgeCount w 0 ((i : ℤ) - n)).filter (0 < ·),
      ((List.range' i₁ (i₂ - i₁)).map fun i : ℕ => edgeCount w 0 ((i : ℤ) - n)).filter (0 < ·),
      ((List.range' i₂ (2 * n - i₂)).map fun i : ℕ => edgeCount w 0 ((i : ℤ) - n)).filter
        (0 < ·), ?_, ?_, ?_, ?_⟩
    · unfold trace
      rw [range_split (2 * n) i₁ i₂ h12 h2N]
      simp only [List.map_append, List.filter_append]
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hx).1
      rw [List.mem_range'_1] at hi
      rw [← Nat.not_odd_iff_even, hodd]; omega
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hx).1
      rw [List.mem_range'_1] at hi
      rw [hodd]; omega
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hx).1
      rw [List.mem_range'_1] at hi
      rw [← Nat.not_odd_iff_even, hodd]; omega

end A048248

