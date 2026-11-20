import Tengoku.Jsp000290Lean.Jsp290.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

/--
@isnad1 id=le.1h2v.s4.eae2a646fe7a from=translated src=- shape=4f48a06f vocab=9eb6b180
-/
theorem prefixSum_ge_index {a : Sequence} (ha : ∀ i, 0 < a i) (N : ℕ) :
    (N : ℤ) ≤ PrefixSum a N := by
  induction N with
  | zero => simp [PrefixSum]
  | succ N ih =>
    rw [prefixSum_succ]
    have := ha N
    push_cast
    omega

/-- The surviving prefix total plus one is a genuine missing integer whenever
the next term exceeds it. The proof retains the original indexed support.
@isnad1 id=le.4h3v.s6.71d79d76d395 from=translated src=- shape=23a1f71b vocab=20299e5b
-/
theorem prefix_slack_after_one {a : Sequence} (ha : ∀ i, 0 ≤ a i)
    (hm : Monotone a) {i N : ℕ} (hiN : i < N)
    (hrep : RepresentsAfter a {i} (PrefixSum a N - a i + 1)) :
    a N ≤ PrefixSum a N - a i + 1 := by
  classical
  by_contra h
  have hlt : PrefixSum a N - a i + 1 < a N := by omega
  obtain ⟨s, hsD, hs⟩ := hrep
  have his : i ∉ s := by
    intro his
    exact disjoint_left.mp hsD his (by simp)
  have hsub : s ⊆ (range N).erase i := by
    intro j hj
    refine mem_erase.mpr ⟨by aesop, mem_range.mpr ?_⟩
    by_contra hNj
    have hNj : N ≤ j := by omega
    have hjle : a j ≤ ∑ k ∈ s, a k := single_le_sum (fun k _ => ha k) hj
    have := hm hNj
    omega
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => ha k)
  have heq := sum_erase_add (range N) a (mem_range.mpr hiN)
  change (∑ k ∈ (range N).erase i, a k) + a i = PrefixSum a N at heq
  omega

/-- Eventual completeness after every single deletion forces diverging slack
for an unbounded positive monotone sequence.
@isnad1 id=divergin.4h1v.s5.15605c7771e7 from=translated src=- shape=2c01f5d0 vocab=f27e666e
-/
theorem divergingSlack_of_one_deletion {a : Sequence}
    (ha : ∀ i, 0 < a i) (hm : Monotone a)
    (hu : ∀ C : ℤ, ∃ i, C < a i)
    (h1 : ∀ i, CompleteAfter a {i}) : DivergingSlack a := by
  intro C
  obtain ⟨i, hi⟩ := hu C
  obtain ⟨T, hT⟩ := h1 i
  obtain ⟨K, hK⟩ := exists_nat_ge (T + a i)
  refine ⟨max (i + 1) K, fun N hN => ?_⟩
  have hiN : i < N := by omega
  have hKN : (K : ℤ) ≤ (N : ℤ) := by exact_mod_cast (show K ≤ N by omega)
  have hSN := prefixSum_ge_index ha N
  have hrep := hT (PrefixSum a N - a i + 1) (by omega)
  have hb := prefix_slack_after_one (fun k => (ha k).le) hm hiN hrep
  omega

/-- A bounded positive sequence has diverging slack without any deletion hypothesis.
@isnad1 id=divergin.2h1v.s5.cf0691eed9ae from=translated src=- shape=13a67be9 vocab=0e9b57ed
-/
theorem divergingSlack_of_bounded {a : Sequence} (ha : ∀ i, 0 < a i)
    (hb : ∃ B : ℤ, ∀ i, a i ≤ B) : DivergingSlack a := by
  obtain ⟨B, hB⟩ := hb
  intro C
  obtain ⟨K, hK⟩ := exists_nat_ge (C + B)
  refine ⟨K, fun N hN => ?_⟩
  have hKN : (K : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hSN := prefixSum_ge_index ha N
  have := hB N
  omega

end Jsp290
