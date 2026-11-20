import Tengoku.Jsp000290Lean.Jsp290.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

/--
@isnad1 id=ex.2h1v.s5.23bfe6b8ee2d from=translated src=- shape=3a86a6c5 vocab=c56b7cd7
-/
theorem monotone_bounded_eventually_constant {a : Sequence} (hm : Monotone a)
    (hb : ∃ B : ℤ, ∀ i, a i ≤ B) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → a n = a K := by
  have hbr : BddAbove (Set.range a) := by
    obtain ⟨B, hB⟩ := hb
    exact ⟨B, by rintro _ ⟨i, rfl⟩; exact hB i⟩
  obtain ⟨v, hv, hmax⟩ := hbr.exists_isGreatest_of_nonempty (Set.range_nonempty a)
  obtain ⟨K, rfl⟩ := hv
  exact ⟨K, fun n hn => le_antisymm (hmax (Set.mem_range_self n)) (hm hn)⟩

/--
@isnad1 id=eq.1h3v.s5.3019d76bf52a from=translated src=- shape=6d14630d vocab=097748c2
-/
theorem prefixSum_constant_tail {a : Sequence} {K : ℕ}
    (hK : ∀ n : ℕ, K ≤ n → a n = a K) (r : ℕ) :
    PrefixSum a (K + r) = PrefixSum a K + (r : ℤ) * a K := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show K + (r + 1) = (K + r) + 1 by omega, prefixSum_succ,
      ih, hK (K + r) (by omega)]
    push_cast
    ring

/--
@isnad1 id=eq.1h3v.s5.cb77bb37af85 from=translated src=- shape=8b5eb459 vocab=ebdd7538
-/
theorem sum_Ico_constant_tail {a : Sequence} {K : ℕ}
    (hK : ∀ n : ℕ, K ≤ n → a n = a K) (r : ℕ) :
    (∑ i ∈ Ico K (K + r), a i) = (r : ℤ) * a K := by
  calc
    (∑ i ∈ Ico K (K + r), a i) = ∑ _i ∈ Ico K (K + r), a K := by
      apply sum_congr rfl
      intro i hi
      exact hK i (mem_Ico.mp hi).1
    _ = (r : ℤ) * a K := by simp [nsmul_eq_mul]

/-- Compress a representation's constant-tail occurrences into a bounded prefix.
@isnad1 id=prefixre.5h4v.s6.c63844d2e999 from=translated src=- shape=2dea524a vocab=d4330074
-/
theorem prefixRep_compress_constant_tail {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    {K r : ℕ} (hpos : 0 < a K)
    (hK : ∀ n : ℕ, K ≤ n → a n = a K)
    {x : ℤ} (hx : Represents a x) (hxr : x ≤ (r : ℤ) * a K) :
    PrefixRep a (K + r) x := by
  classical
  obtain ⟨s, hs⟩ := hx
  let u := s ∩ range K
  let v := s \ range K
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
      _ = _ := by simp [nsmul_eq_mul]
  have hsum : (∑ i ∈ u, a i) + (v.card : ℤ) * a K = x := by
    rw [← hvsum, ← sum_union huv, huvs, hs]
  have hu0 : 0 ≤ ∑ i ∈ u, a i := sum_nonneg (fun i _ => ha i)
  have hvr : v.card ≤ r := by
    by_contra h
    have hlt : (r : ℤ) < (v.card : ℤ) := by exact_mod_cast (show r < v.card by omega)
    nlinarith
  let w := Ico K (K + v.card)
  have huw : Disjoint u w := by
    apply disjoint_left.mpr
    intro i hi hj
    have hiK := mem_range.mp (mem_inter.mp hi).2
    have hjK := (mem_Ico.mp hj).1
    omega
  refine ⟨u ∪ w, ?_, ?_⟩
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact mem_range.mpr (by have := mem_range.mp (mem_inter.mp hi).2; omega)
    · exact mem_range.mpr (by have := (mem_Ico.mp hi).2; omega)
  · rw [sum_union huw]
    change (∑ i ∈ u, a i) + (∑ i ∈ Ico K (K + v.card), a i) = x
    rw [sum_Ico_constant_tail hK v.card]
    exact hsum

/--
@isnad1 id=centrali.3h3v.s5.b7f9d4a58fd6 from=translated src=- shape=81fab1a4 vocab=fd5cb9f7
-/
theorem central_intervals_of_eventually_constant {a : Sequence}
    (ha : ∀ i, 0 < a i) {K : ℕ}
    (hK : ∀ n : ℕ, K ≤ n → a n = a K)
    {T : ℤ} (hc : ∀ x : ℤ, T ≤ x → Represents a x) :
    CentralIntervals a T := by
  have hnonneg : ∀ i, 0 ≤ a i := fun i => (ha i).le
  have hC := prefixSum_nonneg hnonneg K
  refine ⟨K + (PrefixSum a K).toNat, fun N hN x hxlo hxhi => ?_⟩
  have hKN : K ≤ N := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hKN
  have hcr : PrefixSum a K ≤ (r : ℤ) := by
    have : (PrefixSum a K).toNat ≤ r := by omega
    have hcNat : ((PrefixSum a K).toNat : ℤ) = PrefixSum a K := Int.toNat_of_nonneg hC
    have hcast : ((PrefixSum a K).toNat : ℤ) ≤ (r : ℤ) := by exact_mod_cast this
    omega
  have hKr := prefixSum_constant_tail hK r
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hpos := ha K
  have hCr : PrefixSum a K ≤ (r : ℤ) * a K := by nlinarith
  by_cases hxr : x ≤ (r : ℤ) * a K
  · exact prefixRep_compress_constant_tail hnonneg hpos hK (hc x hxlo) hxr
  · have hylo : T ≤ PrefixSum a (K + r) - x := by omega
    have hyhi : PrefixSum a (K + r) - x ≤ (r : ℤ) * a K := by omega
    have hy := prefixRep_compress_constant_tail hnonneg hpos hK
      (hc (PrefixSum a (K + r) - x) hylo) hyhi
    exact PrefixRep.complement_iff.mp hy

/--
@isnad1 id=centrali.4h2v.s6.956c507f04ed from=translated src=- shape=0a808dff vocab=1d7bb8d9
-/
theorem central_intervals_bounded {a : Sequence} (hm : Monotone a)
    (ha : ∀ i, 0 < a i) (hb : ∃ B : ℤ, ∀ i, a i ≤ B)
    {T : ℤ} (hc : ∀ x : ℤ, T ≤ x → Represents a x) :
    CentralIntervals a T := by
  obtain ⟨K, hK⟩ := monotone_bounded_eventually_constant hm hb
  exact central_intervals_of_eventually_constant ha hK hc

end Jsp290
