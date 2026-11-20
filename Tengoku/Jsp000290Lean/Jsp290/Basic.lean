import Tengoku.Jsp000290Lean.Jsp290.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

/--
@isnad1 id=prefixre.0h2v.s3.bd8f76c5a49b from=translated src=- shape=d31a5912 vocab=1f8f10ff
-/
theorem prefixRep_zero (a : Sequence) (N : ℕ) : PrefixRep a N 0 := by
  exact ⟨∅, empty_subset _, by simp⟩

/--
@isnad1 id=represen.0h1v.s3.8731fe968929 from=translated src=- shape=8ba9e24c vocab=386063e2
-/
theorem represents_zero (a : Sequence) : Represents a 0 :=
  ⟨∅, by simp⟩

/--
@isnad1 id=represen.1h3v.s3.6b31bb1e2b4f from=translated src=- shape=7f1401bb vocab=4ed82fd5
-/
theorem PrefixRep.represents {a : Sequence} {N : ℕ} {x : ℤ}
    (h : PrefixRep a N x) : Represents a x := by
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs⟩

/--
@isnad1 id=prefixre.2h4v.s4.bafdc11e103c from=translated src=- shape=e45037fb vocab=6d437374
-/
theorem PrefixRep.mono {a : Sequence} {N M : ℕ} {x : ℤ}
    (h : PrefixRep a N x) (hNM : N ≤ M) : PrefixRep a M x := by
  obtain ⟨s, hs, hx⟩ := h
  exact ⟨s, hs.trans (range_mono hNM), hx⟩

/--
@isnad1 id=eq.0h1v.s4.650b2aebf16b from=translated src=- shape=59ae2d96 vocab=69505d9d
-/
theorem prefixSum_zero (a : Sequence) : PrefixSum a 0 = 0 := by
  simp [PrefixSum]

/--
@isnad1 id=eq.0h2v.s5.c5ea57743079 from=translated src=- shape=39d888a9 vocab=a4290b93
-/
theorem prefixSum_succ (a : Sequence) (N : ℕ) :
    PrefixSum a (N + 1) = PrefixSum a N + a N := by
  simp [PrefixSum, sum_range_succ]

/--
@isnad1 id=prefixre.0h2v.s3.d3dec6c19b6f from=translated src=- shape=24aceb28 vocab=1791ab44
-/
theorem prefixRep_total (a : Sequence) (N : ℕ) :
    PrefixRep a N (PrefixSum a N) := by
  exact ⟨range N, Subset.rfl, rfl⟩

/--
@isnad1 id=prefixre.1h3v.s4.ec462f8c5988 from=translated src=- shape=a2c279c2 vocab=b08e06db
-/
theorem PrefixRep.complement {a : Sequence} {N : ℕ} {x : ℤ}
    (h : PrefixRep a N x) : PrefixRep a N (PrefixSum a N - x) := by
  obtain ⟨s, hs, hx⟩ := h
  refine ⟨range N \ s, sdiff_subset, ?_⟩
  rw [sum_sdiff_eq_sub hs, hx]
  rfl

/--
@isnad1 id=iff.0h3v.s4.225a500e5ee9 from=translated src=- shape=752daf2d vocab=b08e06db
-/
theorem PrefixRep.complement_iff {a : Sequence} {N : ℕ} {x : ℤ} :
    PrefixRep a N (PrefixSum a N - x) ↔ PrefixRep a N x := by
  constructor
  · intro h
    simpa using h.complement
  · exact PrefixRep.complement

/--
@isnad1 id=prefixre.3h5v.s5.1c8746f353ae from=translated src=- shape=f1bdc256 vocab=97d53cd2
-/
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

/--
@isnad1 id=iff.0h2v.s4.6c720cb7289e from=translated src=- shape=d0a75059 vocab=4ed82fd5
-/
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

/--
@isnad1 id=le.1h2v.s4.4b9ca3a08596 from=translated src=- shape=e105a54b vocab=191f3bd1
-/
theorem prefixSum_nonneg {a : Sequence} (ha : ∀ i, 0 ≤ a i) (N : ℕ) :
    0 ≤ PrefixSum a N := by
  exact sum_nonneg (fun i _ => ha i)

/--
@isnad1 id=monotone.1h1v.s5.54af6df45d26 from=translated src=- shape=c80a7580 vocab=0c8158ec
-/
theorem prefixSum_mono {a : Sequence} (ha : ∀ i, 0 ≤ a i) :
    Monotone (PrefixSum a) := by
  intro N M hNM
  exact sum_le_sum_of_subset_of_nonneg (range_mono hNM) (fun i _ _ => ha i)

/--
@isnad1 id=le.2h3v.s5.2dd8f5102670 from=translated src=- shape=318b043a vocab=6d437374
-/
theorem PrefixRep.nonneg {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    {N : ℕ} {x : ℤ} (h : PrefixRep a N x) : 0 ≤ x := by
  obtain ⟨s, hs, rfl⟩ := h
  exact sum_nonneg (fun i _ => ha i)

/--
@isnad1 id=le.2h3v.s5.182981c7502d from=translated src=- shape=b453cd8b vocab=d7d22f46
-/
theorem PrefixRep.le_total {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    {N : ℕ} {x : ℤ} (h : PrefixRep a N x) : x ≤ PrefixSum a N := by
  obtain ⟨s, hs, rfl⟩ := h
  exact sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => ha i)

/--
@isnad1 id=prefixre.4h3v.s5.38920d92494e from=translated src=- shape=51e49afc vocab=c6064f6a
-/
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

/--
@isnad1 id=iff.0h1v.s3.b1f34be0f798 from=translated src=- shape=5dd79605 vocab=7aff2eae
-/
theorem completeAfter_empty {a : Sequence} : CompleteAfter a ∅ ↔ Complete a := by
  simp only [CompleteAfter, Complete, RepresentsAfter, Represents, disjoint_empty_right,
    true_and]

/--
@isnad1 id=complete.2h3v.s4.0db90deeb14d from=translated src=- shape=3f3920b5 vocab=42cd7da4
-/
theorem CompleteAfter.mono {a : Sequence} {D E : Finset ℕ}
    (h : CompleteAfter a E) (hDE : D ⊆ E) : CompleteAfter a D := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨s, hs, hsum⟩ := hT x hx
  exact ⟨s, hs.mono_right hDE, hsum⟩

/--
@isnad1 id=complete.1h2v.s3.e0501f78fa1d from=translated src=- shape=cc170e3a vocab=3caa8731
-/
theorem CompleteAfter.complete {a : Sequence} {D : Finset ℕ}
    (h : CompleteAfter a D) : Complete a :=
  completeAfter_empty.mp (h.mono (empty_subset _))

/--
@isnad1 id=iff.0h2v.s4.a040ccf59373 from=translated src=- shape=1da3459c vocab=1006aa20
-/
theorem not_completeAfter_iff {a : Sequence} {D : Finset ℕ} :
    ¬ CompleteAfter a D ↔ ∀ T : ℤ, ∃ x : ℤ, T ≤ x ∧ ¬ RepresentsAfter a D x := by
  simp only [CompleteAfter, not_exists, not_forall, exists_prop]

end Jsp290
