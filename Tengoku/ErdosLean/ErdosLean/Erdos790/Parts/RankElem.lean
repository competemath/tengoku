import Tengoku.ErdosLean.ErdosLean.Erdos790.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Part: the sorted enumeration `elem` and the rank function `rank` are inverse and monotone. -/

namespace Erdos790

/--
@isnad1 id=ex.1h2v.s6.071e4a20c050 from=translated src=- shape=7b7da895 vocab=2ab5238b
-/
lemma exists_orderEmb_eq (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) :
    ∃ i : Fin A.card, A.orderEmbOfFin rfl i = a := by
  have : a ∈ Set.range (A.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact ha
  exact this

/--
@isnad1 id=eq.0h2v.s6.ee00c7489b0e from=translated src=- shape=5746a958 vocab=feeaa2fc
-/
lemma rank_orderEmb (A : Finset ℤ) (i : Fin A.card) :
    rank A (A.orderEmbOfFin rfl i) = i := by
  unfold rank
  have h : A.filter (· < A.orderEmbOfFin rfl i) =
      (Finset.Iio i).map (A.orderEmbOfFin rfl).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, rfl⟩ := exists_orderEmb_eq A hx
      exact ⟨j, (A.orderEmbOfFin rfl).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem A rfl j, (A.orderEmbOfFin rfl).lt_iff_lt.mpr hj⟩
  rw [h, Finset.card_map, Fin.card_Iio]

/--
@isnad1 id=eq.0h2v.s6.2dc1ee71c169 from=translated src=- shape=e89720b5 vocab=88b5b3e3
-/
lemma elem_eq (A : Finset ℤ) (i : Fin A.card) : elem A i = A.orderEmbOfFin rfl i := by
  unfold elem; simp [i.2]

/--
@isnad1 id=lt.1h2v.s4.d96cc6eb0ee5 from=translated src=- shape=8d21511a vocab=2acdcdbc
-/
theorem rank_lt_card (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) : rank A a < A.card := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  rw [rank_orderEmb]; exact i.2

/--
@isnad1 id=eq.1h2v.s4.95fc4aceec1f from=translated src=- shape=a9a2ab0e vocab=8f1bdda6
-/
theorem elem_rank (A : Finset ℤ) {a : ℤ} (ha : a ∈ A) : elem A (rank A a) = a := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  rw [rank_orderEmb, elem_eq]

/--
@isnad1 id=lt.3h3v.s5.b6986dc81853 from=translated src=- shape=076faa5f vocab=082b99b5
-/
theorem rank_lt_rank (A : Finset ℤ) {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    rank A a < rank A b := by
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq A ha
  obtain ⟨j, rfl⟩ := exists_orderEmb_eq A hb
  rw [rank_orderEmb, rank_orderEmb]
  exact (A.orderEmbOfFin rfl).lt_iff_lt.mp hab

/--
@isnad1 id=lt.2h3v.s4.2a4d4c4baf77 from=translated src=- shape=b24e85be vocab=333c1c99
-/
theorem elem_lt_elem (A : Finset ℤ) {s t : ℕ} (hst : s < t) (ht : t < A.card) :
    elem A s < elem A t := by
  have hs : s < A.card := hst.trans ht
  rw [elem_eq A ⟨s, hs⟩, elem_eq A ⟨t, ht⟩]
  exact (A.orderEmbOfFin rfl).lt_iff_lt.mpr hst

end Erdos790
