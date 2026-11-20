import Tengoku.Jsp000290Lean.Jsp290.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

noncomputable def survivor (D : Finset ℕ) : ℕ → ℕ := Nat.nth (fun i => i ∉ D)

noncomputable def erase (a : Sequence) (D : Finset ℕ) : Sequence :=
  fun n => a (survivor D n)

theorem survivors_infinite (D : Finset ℕ) : {i : ℕ | i ∉ D}.Infinite := by
  have h : {i : ℕ | i ∉ D} = (↑D : Set ℕ)ᶜ := by
    ext i
    simp
  rw [h]
  exact D.finite_toSet.infinite_compl

theorem survivor_strictMono (D : Finset ℕ) : StrictMono (survivor D) :=
  Nat.nth_strictMono (survivors_infinite D)

theorem survivor_not_mem (D : Finset ℕ) (n : ℕ) : survivor D n ∉ D :=
  Nat.nth_mem_of_infinite (survivors_infinite D) n

theorem survivor_count (D : Finset ℕ) {i : ℕ} (hi : i ∉ D) :
    survivor D (Nat.count (fun j => j ∉ D) i) = i :=
  Nat.nth_count hi

theorem represents_erase_iff (a : Sequence) (D : Finset ℕ) (x : ℤ) :
    Represents (erase a D) x ↔ RepresentsAfter a D x := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.image (survivor D), ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi hD
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact survivor_not_mem D j hD
    · rw [Finset.sum_image]
      · exact hs
      · intro i _ j _ hij
        exact (survivor_strictMono D).injective hij
  · rintro ⟨s, hs, hsum⟩
    let c : ℕ → ℕ := Nat.count (fun j => j ∉ D)
    have hnot : ∀ i ∈ s, i ∉ D := fun i hi => Finset.disjoint_left.mp hs hi
    have hleft : ∀ i ∈ s, survivor D (c i) = i := fun i hi => survivor_count D (hnot i hi)
    refine ⟨s.image c, ?_⟩
    calc
      ∑ i ∈ s.image c, erase a D i = ∑ i ∈ s, erase a D (c i) := by
        apply Finset.sum_image
        intro i hi j hj hij
        simpa only [hleft i hi, hleft j hj] using congrArg (survivor D) hij
      _ = ∑ i ∈ s, a i := by
        apply Finset.sum_congr rfl
        intro i hi
        change a (survivor D (c i)) = a i
        rw [hleft i hi]
      _ = x := hsum

theorem complete_erase_iff (a : Sequence) (D : Finset ℕ) :
    Complete (erase a D) ↔ CompleteAfter a D := by
  simp only [Complete, CompleteAfter, represents_erase_iff]

theorem monotone_erase {a : Sequence} (ha : Monotone a) (D : Finset ℕ) :
    Monotone (erase a D) :=
  ha.comp (survivor_strictMono D).monotone

theorem positive_erase {a : Sequence} (ha : ∀ i, 0 < a i) (D : Finset ℕ) :
    ∀ i, 0 < erase a D i := fun i => ha (survivor D i)

theorem sum_survivor_image (a : Sequence) (D : Finset ℕ) (N : ℕ) :
    (∑ i ∈ (range N).image (survivor D), a i) = PrefixSum (erase a D) N := by
  classical
  rw [Finset.sum_image]
  · rfl
  · intro i _ j _ hij
    exact (survivor_strictMono D).injective hij

theorem prefixRep_erase_image {a : Sequence} {D : Finset ℕ} {N : ℕ} {x : ℤ}
    (h : PrefixRep (erase a D) N x) :
    ∃ s : Finset ℕ, s ⊆ (range N).image (survivor D) ∧ ∑ i ∈ s, a i = x := by
  classical
  obtain ⟨s, hs, hsum⟩ := h
  refine ⟨s.image (survivor D), Finset.image_subset_image hs, ?_⟩
  rw [Finset.sum_image]
  · exact hsum
  · intro i _ j _ hij
    exact (survivor_strictMono D).injective hij

theorem image_survivor_range (D : Finset ℕ) (N : ℕ) :
    (range N).image (survivor D) = range (survivor D N) \ D := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr
      (survivor_strictMono D (Finset.mem_range.mp hj)), survivor_not_mem D j⟩
  · intro hi
    obtain ⟨hiN, hiD⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_image.mpr ⟨Nat.count (fun j => j ∉ D) i, ?_, survivor_count D hiD⟩
    apply Finset.mem_range.mpr
    apply (survivor_strictMono D).lt_iff_lt.mp
    rw [survivor_count D hiD]
    exact Finset.mem_range.mp hiN

theorem prefixSum_erase (a : Sequence) (D : Finset ℕ) (N : ℕ)
    (hD : D ⊆ range (survivor D N)) :
    PrefixSum (erase a D) N = PrefixSum a (survivor D N) - ∑ i ∈ D, a i := by
  classical
  unfold PrefixSum erase
  rw [← Finset.sum_image (fun i _ j _ hij => (survivor_strictMono D).injective hij)]
  rw [image_survivor_range]
  exact Finset.sum_sdiff_eq_sub hD

theorem divergingSlack_erase {a : Sequence} (ha : DivergingSlack a) (D : Finset ℕ) :
    DivergingSlack (erase a D) := by
  classical
  intro C
  obtain ⟨N₀, hN₀⟩ := ha (C + ∑ i ∈ D, a i)
  refine ⟨max N₀ (D.sup id + 1), ?_⟩
  intro N hN
  have he : N ≤ survivor D N := (survivor_strictMono D).id_le N
  have hD : D ⊆ range (survivor D N) := by
    intro i hi
    have hi' : i ≤ D.sup id := Finset.le_sup (f := id) hi
    have hN' : D.sup id + 1 ≤ N := (le_max_right _ _).trans hN
    exact Finset.mem_range.mpr (by omega)
  have h := hN₀ (survivor D N) ((le_max_left _ _).trans (hN.trans he))
  rw [prefixSum_erase a D N hD]
  change C ≤ PrefixSum a (survivor D N) - (∑ i ∈ D, a i) - a (survivor D N)
  omega

end Jsp290
