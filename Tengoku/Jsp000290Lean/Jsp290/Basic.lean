import Tengoku.Jsp000290Lean.Jsp290.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

theorem prefixRep_zero (a : Sequence) (N : ℕ) : PrefixRep a N 0 := by
  exact ⟨∅, empty_subset _, by simp⟩

theorem represents_zero (a : Sequence) : Represents a 0 :=
  ⟨∅, by simp⟩

theorem PrefixRep.represents {a : Sequence} {N : ℕ} {x : ℤ}
    (h : PrefixRep a N x) : Represents a x := by
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs⟩

theorem PrefixRep.mono {a : Sequence} {N M : ℕ} {x : ℤ}
    (h : PrefixRep a N x) (hNM : N ≤ M) : PrefixRep a M x := by
  obtain ⟨s, hs, hx⟩ := h
  exact ⟨s, hs.trans (range_mono hNM), hx⟩

theorem prefixSum_zero (a : Sequence) : PrefixSum a 0 = 0 := by
  simp [PrefixSum]

theorem prefixSum_succ (a : Sequence) (N : ℕ) :
    PrefixSum a (N + 1) = PrefixSum a N + a N := by
  simp [PrefixSum, sum_range_succ]

theorem prefixRep_total (a : Sequence) (N : ℕ) :
    PrefixRep a N (PrefixSum a N) := by
  exact ⟨range N, Subset.rfl, rfl⟩

theorem PrefixRep.complement {a : Sequence} {N : ℕ} {x : ℤ}
    (h : PrefixRep a N x) : PrefixRep a N (PrefixSum a N - x) := by
  obtain ⟨s, hs, hx⟩ := h
  refine ⟨range N \ s, sdiff_subset, ?_⟩
  rw [sum_sdiff_eq_sub hs, hx]
  rfl

theorem PrefixRep.complement_iff {a : Sequence} {N : ℕ} {x : ℤ} :
    PrefixRep a N (PrefixSum a N - x) ↔ PrefixRep a N x := by
  constructor
  · intro h
    simpa using h.complement
  · exact PrefixRep.complement

theorem PrefixRep.add_term {a : Sequence} {N M i : ℕ} {x : ℤ}
    (h : PrefixRep a N x) (hNi : N ≤ i) (hiM : i < M) :
    PrefixRep a M (x + a i) := by
  obtain ⟨s, hs, hx⟩ := h
  have his : i ∉ s := by
    intro hi
    have := mem_range.mp (hs hi)
    omega
  refine ⟨insert i s, ?_, ?_⟩
  · intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact mem_range.mpr hiM
    · exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp (hs hj)) (by omega))
  · rw [sum_insert his, hx]
    omega

theorem represents_iff_exists_prefix {a : Sequence} {x : ℤ} :
    Represents a x ↔ ∃ N, PrefixRep a N x := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.sup id + 1, s, ?_, hs⟩
    intro i hi
    apply mem_range.mpr
    have : i ≤ s.sup id := le_sup (f := id) hi
    omega
  · rintro ⟨N, hN⟩
    exact hN.represents

theorem prefixSum_nonneg {a : Sequence} (ha : ∀ i, 0 ≤ a i) (N : ℕ) :
    0 ≤ PrefixSum a N := by
  exact sum_nonneg (fun i _ => ha i)

theorem prefixSum_mono {a : Sequence} (ha : ∀ i, 0 ≤ a i) :
    Monotone (PrefixSum a) := by
  intro N M hNM
  exact sum_le_sum_of_subset_of_nonneg (range_mono hNM) (fun i _ _ => ha i)

theorem PrefixRep.nonneg {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    {N : ℕ} {x : ℤ} (h : PrefixRep a N x) : 0 ≤ x := by
  obtain ⟨s, hs, rfl⟩ := h
  exact sum_nonneg (fun i _ => ha i)

theorem PrefixRep.le_total {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    {N : ℕ} {x : ℤ} (h : PrefixRep a N x) : x ≤ PrefixSum a N := by
  obtain ⟨s, hs, rfl⟩ := h
  exact sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => ha i)

theorem prefixRep_of_represents_lt {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    (hm : Monotone a) {N : ℕ} {x : ℤ} (hx : Represents a x) (hlt : x < a N) :
    PrefixRep a N x := by
  obtain ⟨s, hs⟩ := hx
  refine ⟨s, ?_, hs⟩
  intro i hi
  apply mem_range.mpr
  by_contra hNi
  have hNi : N ≤ i := by omega
  have hai : a i ≤ ∑ j ∈ s, a j := single_le_sum (fun j _ => ha j) hi
  have := hm hNi
  omega

theorem completeAfter_empty {a : Sequence} : CompleteAfter a ∅ ↔ Complete a := by
  simp only [CompleteAfter, Complete, RepresentsAfter, Represents, disjoint_empty_right,
    true_and]

theorem CompleteAfter.mono {a : Sequence} {D E : Finset ℕ}
    (h : CompleteAfter a E) (hDE : D ⊆ E) : CompleteAfter a D := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨s, hs, hsum⟩ := hT x hx
  exact ⟨s, hs.mono_right hDE, hsum⟩

theorem CompleteAfter.complete {a : Sequence} {D : Finset ℕ}
    (h : CompleteAfter a D) : Complete a :=
  completeAfter_empty.mp (h.mono (empty_subset _))

theorem not_completeAfter_iff {a : Sequence} {D : Finset ℕ} :
    ¬ CompleteAfter a D ↔ ∀ T : ℤ, ∃ x : ℤ, T ≤ x ∧ ¬ RepresentsAfter a D x := by
  simp only [CompleteAfter, not_exists, not_forall, exists_prop]

end Jsp290
