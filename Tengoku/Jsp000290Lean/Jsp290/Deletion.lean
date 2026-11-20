import Tengoku.Jsp000290Lean.Jsp290.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

/-- Central subset-sum intervals in finite surviving sets containing any chosen term.-/
def FiniteCentralAfter (a : Sequence) (D : Finset ℕ) : Prop :=
  ∃ T : ℤ, 1 ≤ T ∧ ∀ i : ℕ, i ∉ D →
    ∃ F : Finset ℕ, Disjoint F D ∧ i ∈ F ∧
      ∀ x : ℤ, T ≤ x → x ≤ (∑ k ∈ F, a k) - T →
        ∃ s : Finset ℕ, s ⊆ F ∧ ∑ k ∈ s, a k = x

/--
@isnad1 id=eq.0h3v.s5.21a0a81bfa5c from=translated src=- shape=9f5f3818 vocab=bf378887
-/
theorem sum_inter_add_sum_sdiff (a : Sequence) (s D : Finset ℕ) :
    (∑ i ∈ s ∩ D, a i) + (∑ i ∈ s \ D, a i) = ∑ i ∈ s, a i := by
  have hd : Disjoint (s ∩ D) (s \ D) := by
    apply disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hj).2 (mem_inter.mp hi).2
  have hu : (s ∩ D) ∪ (s \ D) = s := by
    ext i
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  rw [← sum_union hd, hu]

/-- A central interval converts two-deletion robustness into an extra deletable term.
This is the gap argument of Geneson, Lemma 4/Proposition 5, expressed directly
through a missing integer and a three-part decomposition of a representation.
@isnad1 id=ex.4h2v.s6.ad0f381a1522 from=translated src=- shape=6b76987a vocab=764a0caf
-/
theorem deletion_extension_of_central {a : Sequence}
    (ha : ∀ i, 0 ≤ a i) (hu : ∀ C : ℤ, ∃ i, C < a i)
    (h2 : ∀ E : Finset ℕ, E.card = 2 → CompleteAfter a E)
    {D : Finset ℕ} (hc : FiniteCentralAfter a D) :
    ∃ j : ℕ, j ∉ D ∧ CompleteAfter a (insert j D) := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨T, hT, hcentral⟩ := hc
  obtain ⟨i, hi⟩ := hu (2 * T + ∑ k ∈ D, a k)
  have hiD : i ∉ D := by
    intro hiD
    have hle : a i ≤ ∑ k ∈ D, a k := single_le_sum (fun k _ => ha k) hiD
    omega
  obtain ⟨F, hFD, hiF, hF⟩ := hcentral i hiD
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset (D ∪ F)
  have hjD : j ∉ D := by aesop
  have hjF : j ∉ F := by aesop
  have hij : i ≠ j := by aesop
  have hcard : ({i, j} : Finset ℕ).card = 2 := by simp [hij]
  obtain ⟨R, hR⟩ := h2 {i, j} hcard
  obtain ⟨x, hx, hxmissing⟩ := not_completeAfter_iff.mp (hn j hjD) (R + T)
  obtain ⟨s, hsdel, hs⟩ := hR (x - T) (by omega)
  have his : i ∉ s := by
    intro his
    exact disjoint_left.mp hsdel his (by simp)
  have hjs : j ∉ s := by
    intro hjs
    exact disjoint_left.mp hsdel hjs (by simp)
  let g := s ∩ D
  let f := (s \ D) ∩ F
  let q := (s \ D) \ F
  have hsplit : (∑ k ∈ g, a k) + (∑ k ∈ f, a k) +
      (∑ k ∈ q, a k) = x - T := by
    have h₁ := sum_inter_add_sum_sdiff a s D
    have h₂ := sum_inter_add_sum_sdiff a (s \ D) F
    dsimp [g, f, q]
    omega
  have hg0 : 0 ≤ ∑ k ∈ g, a k := sum_nonneg (fun k _ => ha k)
  have hf0 : 0 ≤ ∑ k ∈ f, a k := sum_nonneg (fun k _ => ha k)
  have hg : (∑ k ∈ g, a k) ≤ ∑ k ∈ D, a k := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact inter_subset_right
    · intro k _ _
      exact ha k
  have hfsub : f ⊆ F.erase i := by
    intro k hk
    have hkF : k ∈ F := (mem_inter.mp hk).2
    have hks : k ∈ s := (mem_sdiff.mp (mem_inter.mp hk).1).1
    exact mem_erase.mpr ⟨by aesop, hkF⟩
  have hf : (∑ k ∈ f, a k) ≤ (∑ k ∈ F, a k) - a i := by
    have hle := sum_le_sum_of_subset_of_nonneg hfsub (fun k _ _ => ha k)
    have heq := sum_erase_add F a hiF
    omega
  have hlower : T ≤ x - ∑ k ∈ q, a k := by omega
  have hupper : x - (∑ k ∈ q, a k) ≤ (∑ k ∈ F, a k) - T := by omega
  obtain ⟨t, htF, ht⟩ := hF (x - ∑ k ∈ q, a k) hlower hupper
  have htq : Disjoint t q := by
    apply disjoint_left.mpr
    intro k hkt hkq
    exact (mem_sdiff.mp hkq).2 (htF hkt)
  apply hxmissing
  refine ⟨t ∪ q, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro k hk hkd
    rcases mem_union.mp hk with hkt | hkq
    · have hkF := htF hkt
      rcases mem_insert.mp hkd with rfl | hkD
      · exact hjF hkF
      · exact disjoint_left.mp hFD hkF hkD
    · have hkSD := (mem_sdiff.mp hkq).1
      have hks := (mem_sdiff.mp hkSD).1
      have hkD := (mem_sdiff.mp hkSD).2
      rcases mem_insert.mp hkd with rfl | hkd
      · exact hjs hks
      · exact hkD hkd
  · rw [sum_union htq, ht]
    omega

/--
@isnad1 id=complete.2h3v.s5.cd3d39d0ffa5 from=translated src=- shape=c12bf5dc vocab=970be950
-/
theorem completeAfter_of_smaller_card {a : Sequence} {m : ℕ}
    (hm : ∀ D : Finset ℕ, D.card = m → CompleteAfter a D)
    (D : Finset ℕ) (hD : D.card ≤ m) : CompleteAfter a D := by
  obtain ⟨E, hDE, hE⟩ := Infinite.exists_superset_card_eq D m hD
  exact (hm E hE).mono hDE

/--
@isnad1 id=ex.4h2v.s6.1ad0700af937 from=translated src=- shape=1b1e1be6 vocab=c3d4dabe
-/
theorem deletions_arbitrary_card_of_central {a : Sequence}
    (ha : ∀ i, 0 ≤ a i) (hu : ∀ C : ℤ, ∃ i, C < a i)
    (h2 : ∀ E : Finset ℕ, E.card = 2 → CompleteAfter a E)
    (hc : ∀ D : Finset ℕ, CompleteAfter a D → FiniteCentralAfter a D)
    (n : ℕ) : ∃ D : Finset ℕ, D.card = n ∧ CompleteAfter a D := by
  induction n with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    exact completeAfter_of_smaller_card h2 ∅ (by simp)
  | succ n ih =>
    obtain ⟨D, hD, hcomp⟩ := ih
    obtain ⟨j, hjD, hj⟩ := deletion_extension_of_central ha hu h2 (hc D hcomp)
    exact ⟨insert j D, by simp [card_insert_of_notMem hjD, hD], hj⟩

end Jsp290
