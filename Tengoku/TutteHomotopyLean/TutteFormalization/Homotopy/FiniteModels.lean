import Tengoku.TutteHomotopyLean.TutteFormalization.SeparationRank
import Tengoku.Seed.Combinatorics.Matroid.IndepAxioms
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace TutteFormalization.Homotopy

/-- Finite, executable independence/rank data with proved matroid axioms.
Labels in Fin n are manuscript labels minus one.-/
structure FiniteModel (n : ℕ) where
  independent : Finset (Fin n) → Bool
  rank : Finset (Fin n) → ℕ
  empty_independent : independent ∅ = true
  hereditary : ∀ I J, independent J = true → I ⊆ J → independent I = true
  augmentation : ∀ I J, independent I = true → independent J = true → I.card < J.card →
    ∃ e ∈ J, e ∉ I ∧ independent (insert e I) = true
  rank_bound : ∀ I S, independent I = true → I ⊆ S → I.card ≤ rank S
  rank_attained : ∀ S, ∃ I, I ⊆ S ∧ independent I = true ∧ I.card = rank S

namespace FiniteModel
noncomputable def matroid {n : ℕ} (N : FiniteModel n) : Matroid (Fin n) := by
  classical
  exact (IndepMatroid.ofFinite (Set.finite_univ) (fun I => N.independent I.toFinset = true)
    (by simpa using N.empty_independent)
    (fun {I J} hJ hIJ => N.hereditary _ _ hJ (by simpa using hIJ))
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI, he⟩ := N.augmentation I.toFinset J.toFinset hI hJ
        (by simpa only [Set.ncard_eq_toFinset_card'] using hcard)
      exact ⟨e, by simpa using heJ, by simpa using heI, by simpa using he⟩)
    (fun {_} _ => Set.subset_univ _)).matroid

@[simp] theorem ground {n} (N : FiniteModel n) : N.matroid.E = Set.univ := rfl
instance {n} (N : FiniteModel n) : N.matroid.Finite := ⟨Set.toFinite _⟩

@[simp] theorem indep_iff {n} (N : FiniteModel n) (I : Finset (Fin n)) :
    N.matroid.Indep (I : Set (Fin n)) ↔ N.independent I = true := by
  classical
  simp [matroid, IndepMatroid.matroid_indep_iff]

theorem rank_eq {n} (N : FiniteModel n) (S : Finset (Fin n)) :
    natRank N.matroid S = N.rank S := by
  classical
  obtain ⟨B, hB⟩ := N.matroid.exists_isBasis (S : Set (Fin n)) (by simp)
  have hBr : natRank N.matroid S = B.toFinset.card := by
    simpa only [Set.ncard_eq_toFinset_card'] using natRank_eq_ncard_of_isBasis hB
  have hbind : N.independent B.toFinset = true := hB.indep
  have hupper := N.rank_bound B.toFinset S hbind (by simpa using hB.subset)
  obtain ⟨I, hIS, hI, hr⟩ := N.rank_attained S
  have hIr : natRank N.matroid (I : Set (Fin n)) = I.card := by
    simpa using natRank_eq_ncard_of_isBasis ((N.indep_iff I).mpr hI).isBasis_self
  have hlower := natRank_mono (M := N.matroid) (show (I : Set (Fin n)) ⊆ S by exact hIS)
  omega

/-- Rank-test closure, computable on the finite model.-/
def closure {n} (N : FiniteModel n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun e => N.rank (insert e S) = N.rank S

def Flat {n} (N : FiniteModel n) (S : Finset (Fin n)) : Prop := N.closure S = S
instance {n} (N : FiniteModel n) (S : Finset (Fin n)) : Decidable (N.Flat S) :=
  inferInstanceAs (Decidable (N.closure S = S))
end FiniteModel

/-- Explicit names of the three four-circuits of the labelled bipartite model.-/
def fourCircuits : Finset (Finset (Fin 6)) := {{0,1,3,4}, {0,2,3,5}, {1,2,4,5}}
def bipartiteIndependent (I : Finset (Fin 6)) : Bool :=
  decide (I.card ≤ 3 ∨ (I.card = 4 ∧ I ∉ fourCircuits))
def bipartiteRank (I : Finset (Fin 6)) : ℕ :=
  if I.card ≤ 3 then I.card else if I ∈ fourCircuits then 3 else 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
def bipartiteModel : FiniteModel 6 where
  independent := bipartiteIndependent
  rank := bipartiteRank
  empty_independent := by decide
  hereditary := by decide
  augmentation := by decide
  rank_bound := by decide
  rank_attained := by decide

/-- The four uniform lattices used in the first three families.-/
def uniformIndependent (r : ℕ) {n : ℕ} (I : Finset (Fin n)) : Bool := decide (I.card ≤ r)
def uniformRank (r : ℕ) {n : ℕ} (I : Finset (Fin n)) : ℕ := min I.card r

set_option maxRecDepth 100000 in
def u22 : FiniteModel 2 where
  independent := uniformIndependent 2
  rank := uniformRank 2
  empty_independent := by decide
  hereditary := by decide
  augmentation := by decide
  rank_bound := by decide
  rank_attained := by decide

set_option maxRecDepth 100000 in
def u23 : FiniteModel 3 where
  independent := uniformIndependent 2
  rank := uniformRank 2
  empty_independent := by decide
  hereditary := by decide
  augmentation := by decide
  rank_bound := by decide
  rank_attained := by decide

set_option maxRecDepth 100000 in
def u33 : FiniteModel 3 where
  independent := uniformIndependent 3
  rank := uniformRank 3
  empty_independent := by decide
  hereditary := by decide
  augmentation := by decide
  rank_bound := by decide
  rank_attained := by decide

set_option maxRecDepth 100000 in
def u34 : FiniteModel 4 where
  independent := uniformIndependent 3
  rank := uniformRank 3
  empty_independent := by decide
  hereditary := by decide
  augmentation := by decide
  rank_bound := by decide
  rank_attained := by decide

end TutteFormalization.Homotopy
