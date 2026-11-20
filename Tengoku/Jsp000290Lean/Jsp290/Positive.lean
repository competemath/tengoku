import Tengoku.Jsp000290Lean.Jsp290.Central
import Tengoku.Jsp000290Lean.Jsp290.CentralBounded
import Tengoku.Jsp000290Lean.Jsp290.Reindex
import Tengoku.Jsp000290Lean.Jsp290.Slack
import Tengoku.Jsp000290Lean.Jsp290.Deletion
import Tengoku.Jsp000290Lean.Jsp290.BoundedDeletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Jsp290

open Finset

theorem central_intervals {a : Sequence} (hm : Monotone a)
    (ha : ∀ i, 0 < a i) {T : ℤ} (hT : 1 ≤ T)
    (hc : ∀ x : ℤ, T ≤ x → Represents a x) (hd : DivergingSlack a) :
    CentralIntervals a T := by
  by_cases hu : ∀ C : ℤ, ∃ i : ℕ, C < a i
  · exact Central.central_intervals_unbounded hm ha hT hc hd hu
  · have hb : ∃ B : ℤ, ∀ i, a i ≤ B := by
      push_neg at hu
      exact hu
    exact central_intervals_bounded hm ha hb hc

theorem finiteCentralAfter_of_slack {a : Sequence}
    (hm : Monotone a) (ha : ∀ i, 0 < a i) (hd : DivergingSlack a)
    {D : Finset ℕ} (hc : CompleteAfter a D) : FiniteCentralAfter a D := by
  classical
  obtain ⟨T₀, hT₀⟩ := (complete_erase_iff a D).mpr hc
  let T : ℤ := max 1 T₀
  have hT : 1 ≤ T := le_max_left _ _
  have hrep : ∀ x : ℤ, T ≤ x → Represents (erase a D) x := by
    intro x hx
    exact hT₀ x ((le_max_right _ _).trans hx)
  obtain ⟨N₀, hN₀⟩ := central_intervals (monotone_erase hm D)
    (positive_erase ha D) hT hrep (divergingSlack_erase hd D)
  refine ⟨T, hT, ?_⟩
  intro i hiD
  let k := Nat.count (fun j => j ∉ D) i
  let N := max N₀ (k + 1)
  refine ⟨(range N).image (survivor D), ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro j hj hjD
    obtain ⟨l, _, rfl⟩ := mem_image.mp hj
    exact survivor_not_mem D l hjD
  · apply mem_image.mpr
    refine ⟨k, mem_range.mpr ?_, survivor_count D hiD⟩
    have h : k + 1 ≤ N := le_max_right _ _
    omega
  · intro x hx hxupper
    rw [sum_survivor_image] at hxupper
    exact prefixRep_erase_image (hN₀ N (le_max_left _ _) x hx hxupper)

/-- Two-deletion robustness allows some deletion of every finite size.-/
theorem positive_deletions_arbitrary_card {a : Sequence}
    (hm : Monotone a) (ha : ∀ i, 0 < a i)
    (h2 : ∀ D : Finset ℕ, D.card = 2 → CompleteAfter a D)
    (n : ℕ) : ∃ D : Finset ℕ, D.card = n ∧ CompleteAfter a D := by
  by_cases hu : ∀ C : ℤ, ∃ i : ℕ, C < a i
  · have h1 : ∀ i, CompleteAfter a {i} := by
      intro i
      exact completeAfter_of_smaller_card h2 {i} (by simp)
    have hd := divergingSlack_of_one_deletion ha hm hu h1
    exact deletions_arbitrary_card_of_central (fun i => le_of_lt (ha i)) hu h2
      (fun _ hc => finiteCentralAfter_of_slack hm ha hd hc) n
  · have hb : ∃ B : ℤ, ∀ i, a i ≤ B := by
      push_neg at hu
      exact hu
    have hc : Complete a :=
      (completeAfter_of_smaller_card h2 ∅ (by simp)).complete
    exact exists_completeAfter_card_bounded hm hb hc n

theorem positive_exclusion {a : Sequence} (hm : Monotone a)
    (ha : ∀ i, 0 < a i) {m n : ℕ} (hm2 : 2 ≤ m)
    (hrobust : ∀ D : Finset ℕ, D.card = m → CompleteAfter a D)
    (hfail : ∀ D : Finset ℕ, D.card = n → ¬ CompleteAfter a D) : False := by
  have h2 : ∀ D : Finset ℕ, D.card = 2 → CompleteAfter a D := by
    intro D hD
    exact completeAfter_of_smaller_card hrobust D (by omega)
  obtain ⟨D, hD, hc⟩ := positive_deletions_arbitrary_card hm ha h2 n
  exact hfail D hD hc

end Jsp290
