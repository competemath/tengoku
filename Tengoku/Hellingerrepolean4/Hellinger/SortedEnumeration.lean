import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Finset.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! An actual sorted enumeration of a finite type, preserving every element.
Ties in the score are retained with their full multiplicity. -/

set_option autoImplicit false
noncomputable section

namespace Hellinger.SortedEnumeration

variable {α : Type*} [Fintype α]

def sortedList (score : α → ℕ) : List α :=
  Finset.univ.toList.mergeSort (fun a b => decide (score a ≤ score b))

/--
@isnad1 id=eq.0h2v.s4.f5712360be10 from=translated src=- shape=a3dad467 vocab=ef12ae08
-/
theorem sortedList_length (score : α → ℕ) : (sortedList score).length = Fintype.card α := by
  simp [sortedList]

/--
@isnad1 id=nodup.0h2v.s3.9956dd9ac543 from=translated src=- shape=004779e3 vocab=af3171c1
-/
theorem sortedList_nodup (score : α → ℕ) : (sortedList score).Nodup := by
  exact (List.mergeSort_perm Finset.univ.toList _).nodup_iff.mpr Finset.univ.nodup_toList

/--
@isnad1 id=mem.0h3v.s4.24c89bfc52ad from=translated src=- shape=33e11122 vocab=86beceb9
-/
theorem mem_sortedList (score : α → ℕ) (x : α) : x ∈ sortedList score := by
  simp [sortedList]

/--
@isnad1 id=pairwise.0h2v.s4.b5f6e25a4f25 from=translated src=- shape=5100725a vocab=0bc4f806
-/
theorem sortedList_pairwise (score : α → ℕ) :
    (sortedList score).Pairwise (fun a b => score a ≤ score b) := by
  simpa only [sortedList, decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (fun a b c (hab : decide (score a ≤ score b) = true)
        (hbc : decide (score b ≤ score c) = true) => by
        simpa only [decide_eq_true_eq] using
          le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (score a) (score b))
      Finset.univ.toList)

variable [DecidableEq α]

def sortedEquiv (score : α → ℕ) : Fin (Fintype.card α) ≃ α :=
  (finCongr (sortedList_length score).symm).trans
    (List.Nodup.getEquivOfForallMemList (sortedList score) (sortedList_nodup score)
      (mem_sortedList score))

/--
@isnad1 id=monotone.0h2v.s6.d88e8469996a from=translated src=- shape=4ad8e3f3 vocab=c284faec
-/
theorem sortedEquiv_monotone (score : α → ℕ) :
    Monotone (fun i => score (sortedEquiv score i)) := by
  intro i j hij
  apply (sortedList_pairwise score).rel_get_of_le
  exact hij

/--
@isnad1 id=eq.0h3v.s7.5719578fc1cb from=translated src=- shape=6f1f801f vocab=437c89e4
-/
theorem card_filter_sortedEquiv (score : α → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin (Fintype.card α) => score (sortedEquiv score i) = k)).card =
      (Finset.univ.filter (fun x : α => score x = k)).card := by
  apply Finset.card_bij (fun i _ => sortedEquiv score i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i _ j _ hij
    exact (sortedEquiv score).injective hij
  · intro x hx
    refine ⟨(sortedEquiv score).symm x, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] using hx

end Hellinger.SortedEnumeration
