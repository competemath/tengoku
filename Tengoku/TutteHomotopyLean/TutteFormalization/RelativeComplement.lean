import Tengoku.TutteHomotopyLean.TutteFormalization.FlatRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
ST-05: the relative complement construction in `lem:flat-complement`.
The recursion is the paper's simultaneous adjoining of an element to S and T;
it terminates because the corank of S decreases strictly at each step.
-/

namespace TutteFormalization

variable {α : Type*} {M : Matroid α} [M.Finite]

/--
@isnad1 id=eq.3h4v.s6.688ab01e4765 from=translated src=- shape=92fd3ebf vocab=4a76c35f
-/
theorem natRank_closure_insert {S : Set α} (hS : M.IsFlat S) {e : α}
    (he : e ∈ M.E) (heS : e ∉ S) :
    natRank M (M.closure (insert e S)) = natRank M S + 1 := by
  rw [natRank_closure]
  have hr : M.eRk (insert e S) = M.eRk S + 1 :=
    M.eRk_insert_eq_add_one ⟨he, by simpa only [hS.closure] using heS⟩
  rw [← cast_natRank M (insert e S), ← cast_natRank M S] at hr
  exact_mod_cast hr

/-- ST-05: recursive construction before the final intersection calculation.
The additive rank equation avoids truncated subtraction in the invariant.
@isnad1 id=ex.3h4v.s6.1d13f999a642 from=translated src=- shape=d8e3f738 vocab=0bc9a793
-/
theorem exists_relative_complement_data (S T : Set α)
    (hS : M.IsFlat S) (hT : M.IsFlat T) (hTS : T ⊆ S) :
    ∃ U : Set α, M.IsFlat U ∧ T ⊆ U ∧ M.closure (U ∪ S) = M.E ∧
      natRank M U + natRank M S = natRank M T + natRank M M.E := by
  generalize hn : natRank M M.E - natRank M S = n
  induction n using Nat.strong_induction_on generalizing S T with
  | h n ih =>
    by_cases hSE : S = M.E
    · subst S
      exact ⟨T, hT, Set.Subset.rfl, by simp [Set.union_eq_right.mpr hT.subset_ground], rfl⟩
    have hnsub : ¬ M.E ⊆ S := fun h => hSE (Set.Subset.antisymm hS.subset_ground h)
    obtain ⟨e, heE, heS⟩ := Set.not_subset.mp hnsub
    let S' := M.closure (insert e S)
    let T' := M.closure (insert e T)
    have hS' : M.IsFlat S' := M.isFlat_closure _
    have hT' : M.IsFlat T' := M.isFlat_closure _
    have hT'S' : T' ⊆ S' := M.closure_mono (Set.insert_subset_insert hTS)
    have hSr : natRank M S' = natRank M S + 1 := natRank_closure_insert hS heE heS
    have hTr : natRank M T' = natRank M T + 1 :=
      natRank_closure_insert hT heE (fun heT => heS (hTS heT))
    have hSbound : natRank M S' ≤ natRank M M.E := natRank_mono hS'.subset_ground
    have hdec : natRank M M.E - natRank M S' < n := by omega
    obtain ⟨U, hU, hT'U, hjoin, hr⟩ :=
      ih (natRank M M.E - natRank M S') hdec S' T' hS' hT' hT'S' rfl
    have hTT' : T ⊆ T' := (Set.subset_insert e T).trans
      (M.subset_closure _ (Set.insert_subset heE hT.subset_ground))
    have heU : e ∈ U := hT'U (M.subset_closure _
      (Set.insert_subset heE hT.subset_ground) (Set.mem_insert e T))
    have hjoin' : M.closure (U ∪ S) = M.E := by
      have heq : U ∪ insert e S = U ∪ S := by
        ext x
        simp only [Set.mem_union, Set.mem_insert_iff]
        aesop
      simpa only [S', M.closure_union_closure_right_eq, heq] using hjoin
    exact ⟨U, hU, hTT'.trans hT'U, hjoin', by omega⟩

/-- ST-05: full relative complement, with the source corank formula.
@isnad1 id=ex.3h4v.s6.d15526b6b83c from=translated src=- shape=22ffece6 vocab=fd4c24fd
-/
theorem exists_relative_complement (S T : Set α)
    (hS : M.IsFlat S) (hT : M.IsFlat T) (hTS : T ⊆ S) :
    ∃ U : Set α, M.IsFlat U ∧ T ⊆ U ∧ U ∩ S = T ∧ M.closure (U ∪ S) = M.E ∧
      natRank M M.E - natRank M U = natRank M S - natRank M T := by
  obtain ⟨U, hU, hTU, hjoin, hr⟩ := exists_relative_complement_data S T hS hT hTS
  have hsub : natRank M (U ∩ S) + natRank M M.E ≤ natRank M U + natRank M S := by
    simpa only [hjoin] using natRank_submodular M U S
  have hinter : U ∩ S = T := (flat_eq_of_subset_of_natRank_le hT (flat_inter hU hS)
    (Set.subset_inter hTU hTS) (by omega)).symm
  exact ⟨U, hU, hTU, hinter, hjoin, by omega⟩

end TutteFormalization
