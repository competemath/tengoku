import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.ThorpCompatibility.PermutationProbability

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
def MeetsLists {α β : Type*} (S : β × β → Finset α) (r : α → Equiv.Perm β) : Prop :=
  ∀ j k i, i ∈ S (j, k) → r i j = k

lemma lists_incidence_count {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

    (S : β × β → Finset α) (r : α → Equiv.Perm β) (hr : MeetsLists S r) :
    ∑ i, (Finset.univ.filter (fun j => i ∈ S (j, r i j))).card =
      ∑ b, (S b).card := by
  have hk (i : α) (j k : β) : i ∈ S (j, k) ↔ k = r i j ∧ i ∈ S (j, r i j) := by
    constructor
    · intro h
      exact ⟨(hr j k i h).symm, by simpa [hr j k i h] using h⟩
    · rintro ⟨rfl, h⟩
      exact h
  have hc (s : Finset α) : s.card = ∑ i, if i ∈ s then 1 else 0 := by simp
  calc
    _ = ∑ i, ∑ j, ∑ k, if i ∈ S (j, k) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro j _
      symm
      calc
        _ = ∑ k, if k = r i j then (if i ∈ S (j, r i j) then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases he : k = r i j
          · subst k
            simp
          · have hmem : i ∉ S (j, k) := fun h => he (hr j k i h).symm
            simp [he, hmem]
        _ = _ := by simp
    _ = ∑ j, ∑ k, ∑ i, if i ∈ S (j, k) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type, hc]

end ThorpCompatibility

end OAI
