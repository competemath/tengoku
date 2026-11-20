import Tengoku.Jsp000290Lean.Jsp290.CentralBounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

/-- Deleting finitely many copies from an infinite constant tail preserves all
subset sums, even when that constant is zero or negative.
@isnad1 id=represen.3h4v.s5.b1bc6c5a6465 from=translated src=- shape=bc84b979 vocab=64b0240f
-/
theorem representsAfter_of_constant_tail {a : Sequence} {K : ℕ}
    (hK : ∀ n : ℕ, K ≤ n → a n = a K)
    {D : Finset ℕ} (hD : ∀ i ∈ D, K ≤ i)
    {x : ℤ} (hx : Represents a x) : RepresentsAfter a D x := by
  classical
  obtain ⟨s, hs⟩ := hx
  let u := s ∩ range K
  let v := s \ range K
  let M := max K (D.sup id + 1)
  let w := Ico M (M + v.card)
  have huv : Disjoint u v := by
    apply disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hj).2 (mem_inter.mp hi).2
  have huvs : u ∪ v = s := by
    ext i
    simp only [u, v, mem_union, mem_inter, mem_sdiff]
    tauto
  have hvsum : (∑ i ∈ v, a i) = (v.card : ℤ) * a K := by
    calc
      (∑ i ∈ v, a i) = ∑ _i ∈ v, a K := by
        apply sum_congr rfl
        intro i hi
        apply hK
        have := (mem_sdiff.mp hi).2
        simp only [mem_range] at this
        omega
      _ = _ := by simp
  have hKM : K ≤ M := le_max_left _ _
  have hwval : (∑ i ∈ w, a i) = (v.card : ℤ) * a K := by
    calc
      (∑ i ∈ w, a i) = ∑ _i ∈ w, a K := by
        apply sum_congr rfl
        intro i hi
        exact hK i (le_trans hKM (mem_Ico.mp hi).1)
      _ = _ := by simp [w]
  have huw : Disjoint u w := by
    apply disjoint_left.mpr
    intro i hi hj
    have hilt := mem_range.mp (mem_inter.mp hi).2
    have hM := (mem_Ico.mp hj).1
    omega
  refine ⟨u ∪ w, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro i hi hiD
    rcases mem_union.mp hi with hi | hi
    · have hilt := mem_range.mp (mem_inter.mp hi).2
      have := hD i hiD
      omega
    · have himax : i ≤ D.sup id := le_sup (f := id) hiD
      have hiM : M ≤ i := (mem_Ico.mp hi).1
      have hM : D.sup id + 1 ≤ M := le_max_right _ _
      omega
  · rw [sum_union huw, hwval, ← hvsum, ← sum_union huv, huvs, hs]

/--
@isnad1 id=complete.3h3v.s5.6eb7a8bbc0d8 from=translated src=- shape=cf915241 vocab=aed1f7a0
-/
theorem completeAfter_of_constant_tail {a : Sequence} {K : ℕ}
    (hK : ∀ n : ℕ, K ≤ n → a n = a K)
    {D : Finset ℕ} (hD : ∀ i ∈ D, K ≤ i)
    (hc : Complete a) : CompleteAfter a D := by
  obtain ⟨T, hT⟩ := hc
  exact ⟨T, fun x hx => representsAfter_of_constant_tail hK hD (hT x hx)⟩

/--
@isnad1 id=ex.3h2v.s5.16b02cbfbd08 from=translated src=- shape=48b90bd0 vocab=cc9bfab8
-/
theorem exists_completeAfter_card_bounded {a : Sequence}
    (hm : Monotone a) (hb : ∃ B : ℤ, ∀ i, a i ≤ B) (hc : Complete a)
    (n : ℕ) : ∃ D : Finset ℕ, D.card = n ∧ CompleteAfter a D := by
  obtain ⟨K, hK⟩ := monotone_bounded_eventually_constant hm hb
  refine ⟨Ico K (K + n), by simp, ?_⟩
  exact completeAfter_of_constant_tail hK (fun i hi => (mem_Ico.mp hi).1) hc

end Jsp290
