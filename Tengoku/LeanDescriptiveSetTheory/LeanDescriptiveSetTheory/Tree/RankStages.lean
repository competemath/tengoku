/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Code
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Hierarchy
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.CodeSpace
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel stages of the well-founded-tree rank

For a finite node `s`, `nodeRankLT i s` contains precisely the coded trees in which `s` is an
accessible node of local accessibility rank strictly below `i`. The definition is local: a code
may belong to a node stage even when an unrelated branch is ill-founded. This locality gives exact
zero, successor, and limit equations.

The whole-tree stage `treeRankLT i` contains only well-founded decoded trees whose root rank is
strictly below `i`. At every positive level it is the union of the root-absent code and the local
root stage. Consequently every countable stage is Borel and has a `BorelCode` witness.

The strict inequality convention is part of the public API. No claim about optimal Borel rank is
made.
-/

open Cardinal Ordinal Set

namespace DescriptiveSetTheory.Tree

/-- Codes in which `s` is accessible and has local accessibility rank strictly below `i`.-/
def nodeRankLT (i : Ordinal.{0}) (s : List ℕ) : Set TreeCode :=
  {c | ∃ hs : s ∈ decodeTree c,
    ∃ h : Acc (Child (decodeTree c)) (⟨s, hs⟩ : decodeTree c), h.rank < i}

/-- The zero local-rank stage is empty.-/
@[simp] theorem nodeRankLT_zero (s : List ℕ) : nodeRankLT 0 s = ∅ := by
  ext c
  simp [nodeRankLT]

/-- Local node stages are monotone in their ordinal bound.-/
theorem nodeRankLT_mono {i j : Ordinal.{0}} (hij : i ≤ j) (s : List ℕ) :
    nodeRankLT i s ⊆ nodeRankLT j s := by
  rintro c ⟨hs, h, hrank⟩
  exact ⟨hs, h, hrank.trans_le hij⟩

/-- Exact successor recursion for local node-rank stages.-/
theorem nodeRankLT_succ (i : Ordinal.{0}) (s : List ℕ) :
    nodeRankLT (Order.succ i) s =
      {c | s ∈ decodeTree c} ∩
        ⋂ a : ℕ, ({c | s ++ [a] ∉ decodeTree c} ∪ nodeRankLT i (s ++ [a])) := by
  ext c
  constructor
  · rintro ⟨hs, h, hrank⟩
    refine ⟨hs, Set.mem_iInter.2 fun a => ?_⟩
    by_cases hchild : s ++ [a] ∈ decodeTree c
    · refine Or.inr ⟨hchild, h.inv ⟨a, rfl⟩, ?_⟩
      exact (Acc.rank_lt_of_rel h ⟨a, rfl⟩).trans_le (Order.lt_succ_iff.mp hrank)
    · exact Or.inl hchild
  · rintro ⟨hs, hall⟩
    have hchild : ∀ (a : ℕ) (ha : s ++ [a] ∈ decodeTree c),
        ∃ h : Acc (Child (decodeTree c))
            (⟨s ++ [a], ha⟩ : decodeTree c), h.rank < i := by
      intro a ha
      rcases Set.mem_iInter.1 hall a with hmissing | hstage
      · exact (hmissing ha).elim
      · rcases hstage with ⟨_, h, hrank⟩
        exact ⟨h, hrank⟩
    let hroot : Acc (Child (decodeTree c)) (⟨s, hs⟩ : decodeTree c) :=
      Acc.intro _ fun t ht => by
        obtain ⟨a, ha⟩ := ht
        have hmem : s ++ [a] ∈ decodeTree c := by
          rw [← ha]
          exact t.property
        obtain ⟨h, _⟩ := hchild a hmem
        have htEq : t = (⟨s ++ [a], hmem⟩ : decodeTree c) := Subtype.ext ha
        simpa [htEq] using h
    refine ⟨hs, hroot, Order.lt_succ_iff.mpr ?_⟩
    rw [hroot.rank_eq]
    refine Ordinal.iSup_le fun t => ?_
    obtain ⟨a, ha⟩ := t.property
    have hmem : s ++ [a] ∈ decodeTree c := by
      rw [← ha]
      exact t.1.property
    obtain ⟨h, hrank⟩ := hchild a hmem
    have htEq : t.1 = (⟨s ++ [a], hmem⟩ : decodeTree c) := Subtype.ext ha
    have h' : Acc (Child (decodeTree c)) t.1 := by
      simpa [htEq] using h
    have hrank' : h'.rank < i := by
      simpa [htEq] using hrank
    rw [Subsingleton.elim (hroot.inv t.property) h']
    exact Order.succ_le_iff.mpr hrank'

/-- At a nonzero limit, a local stage is the union of all earlier local stages.-/
theorem nodeRankLT_limit {i : Ordinal.{0}} (hi : Order.IsSuccLimit i) (s : List ℕ) :
    nodeRankLT i s = ⋃ j : Set.Iio i, nodeRankLT j.1 s := by
  ext c
  constructor
  · rintro ⟨hs, h, hrank⟩
    refine Set.mem_iUnion.2 ⟨⟨Order.succ h.rank, hi.succ_lt hrank⟩, ?_⟩
    exact ⟨hs, h, Order.lt_succ h.rank⟩
  · intro hc
    rcases Set.mem_iUnion.1 hc with ⟨j, hs, h, hrank⟩
    exact ⟨hs, h, hrank.trans j.property⟩

/-- Membership of a fixed node is clopen in the coded tree space.-/
theorem isClopen_nodeMem (s : List ℕ) : IsClopen {c : TreeCode | s ∈ decodeTree c} := by
  have hcontinuous : Continuous (fun c : TreeCode => c.1 s) :=
    (continuous_listNatBoolCoordinate s).comp continuous_subtype_val
  have heq : {c : TreeCode | s ∈ decodeTree c} =
      (fun c : TreeCode => c.1 s) ⁻¹' ({true} : Set Bool) := by
    ext c
    simp
  rw [heq]
  exact (isClopen_discrete ({true} : Set Bool)).preimage hcontinuous

/-- Every countable local node-rank stage is Borel measurable.-/
theorem borelMeasurableSet_nodeRankLT {i : Ordinal.{0}} (hi : IsCountableBorelLevel i)
    (s : List ℕ) : @MeasurableSet TreeCode (borel TreeCode) (nodeRankLT i s) := by
  induction i using WellFoundedLT.induction generalizing s with
  | ind i ih =>
      rcases Ordinal.zero_or_succ_or_isSuccLimit i with rfl | ⟨j, rfl⟩ | hlim
      · simp
      · rw [nodeRankLT_succ]
        have hnode : @MeasurableSet TreeCode (borel TreeCode)
            {c | s ∈ decodeTree c} :=
          MeasurableSpace.GenerateMeasurable.basic _ (isClopen_nodeMem s).isOpen
        refine hnode.inter (MeasurableSet.iInter fun a => ?_)
        have hchild : @MeasurableSet TreeCode (borel TreeCode)
            {c | s ++ [a] ∈ decodeTree c} :=
          MeasurableSpace.GenerateMeasurable.basic _ (isClopen_nodeMem (s ++ [a])).isOpen
        exact hchild.compl.union
          (ih j (Order.lt_succ j) ((Order.lt_succ j).trans hi) (s ++ [a]))
      · letI : Countable (Set.Iio i) := countable_Iio_of_isCountableBorelLevel hi
        rw [nodeRankLT_limit hlim]
        exact MeasurableSet.iUnion fun j => ih j.1 j.2 (j.2.trans hi) s

/-- A root accessibility proof makes every node of a prefix-closed tree accessible.-/
private theorem acc_of_root {T : Descriptive.tree ℕ} (hroot : [] ∈ T)
    (hacc : Acc (Child T) (⟨[], hroot⟩ : T)) (s : List ℕ) (hs : s ∈ T) :
    Acc (Child T) (⟨s, hs⟩ : T) := by
  induction s using List.reverseRecOn with
  | nil => simpa using hacc
  | append_singleton s a ih =>
      exact (ih (T.property hs)).inv ⟨a, rfl⟩

/-- The global node rank agrees with any local accessibility proof's rank.-/
private theorem nodeRank_eq_accRank {T : Descriptive.tree ℕ} (hT : IsWellFounded T)
    (s : T) (hacc : Acc (Child T) s) : nodeRank hT s = hacc.rank := by
  letI : _root_.IsWellFounded T (Child T) := ⟨hT⟩
  unfold nodeRank _root_.IsWellFounded.rank
  rw [Subsingleton.elim (_root_.IsWellFounded.apply (Child T) s) hacc]

/-- Local accessibility of the root is equivalent to well-foundedness of the whole tree.-/
theorem acc_root_iff_isWellFounded {T : Descriptive.tree ℕ} (hroot : [] ∈ T) :
    Acc (Child T) (⟨[], hroot⟩ : T) ↔ IsWellFounded T := by
  constructor
  · intro hacc
    change WellFounded (Child T)
    exact WellFounded.intro fun t : T => by
      simpa using acc_of_root hroot hacc t.1 t.2
  · intro hT
    change WellFounded (Child T) at hT
    exact hT.apply (⟨[], hroot⟩ : T)

/-- The strict whole-tree rank stage; ill-founded codes are excluded by definition.-/
def treeRankLT (i : Ordinal.{0}) : Set TreeCode :=
  {c | ∃ hT : IsWellFounded (decodeTree c), rank (decodeTree c) hT < i}

/-- Unfolded membership in a strict whole-tree rank stage.-/
theorem mem_treeRankLT {i : Ordinal.{0}} {c : TreeCode} :
    c ∈ treeRankLT i ↔
      ∃ hT : IsWellFounded (decodeTree c), rank (decodeTree c) hT < i :=
  Iff.rfl

/-- The non-strict formulation is derived from the strict convention at a successor bound.-/
theorem mem_treeRankLT_succ_iff_le {i : Ordinal.{0}} {c : TreeCode} :
    c ∈ treeRankLT (Order.succ i) ↔
      ∃ hT : IsWellFounded (decodeTree c), rank (decodeTree c) hT ≤ i := by
  constructor
  · rintro ⟨hT, hrank⟩
    exact ⟨hT, Order.lt_succ_iff.mp hrank⟩
  · rintro ⟨hT, hrank⟩
    exact ⟨hT, Order.lt_succ_iff.mpr hrank⟩

/-- The zero whole-tree rank stage is empty.-/
@[simp] theorem treeRankLT_zero : treeRankLT 0 = ∅ := by
  ext c
  simp [treeRankLT]

/-- At a positive bound, a whole-tree stage is the root-absent locus union the local root stage.-/
theorem treeRankLT_eq_root {i : Ordinal.{0}} (hi : 0 < i) :
    treeRankLT i = {c | [] ∉ decodeTree c} ∪ nodeRankLT i [] := by
  ext c
  constructor
  · rintro ⟨hT, hrank⟩
    by_cases hroot : [] ∈ decodeTree c
    · have hacc : Acc (Child (decodeTree c)) (⟨[], hroot⟩ : decodeTree c) :=
        (acc_root_iff_isWellFounded hroot).2 hT
      refine Or.inr ⟨hroot, hacc, ?_⟩
      calc
        hacc.rank = nodeRank hT ⟨[], hroot⟩ := (nodeRank_eq_accRank hT _ hacc).symm
        _ = rank (decodeTree c) hT := (rank_eq_nodeRank hT hroot).symm
        _ < i := hrank
    · exact Or.inl hroot
  · rintro (hroot | hstage)
    · have hbot : decodeTree c = ⊥ := Descriptive.Tree.tree_eq_bot.mpr hroot
      have hT : IsWellFounded (decodeTree c) := by
        rw [hbot]
        exact (isWellFounded_iff_body_eq_empty.mpr body_bot)
      refine ⟨hT, ?_⟩
      rw [rank_eq_zero_of_nil_not_mem hT hroot]
      exact hi
    · rcases hstage with ⟨hroot, hacc, hrank⟩
      have hT : IsWellFounded (decodeTree c) :=
        (acc_root_iff_isWellFounded hroot).1 hacc
      refine ⟨hT, ?_⟩
      rw [rank_eq_nodeRank hT hroot]
      rw [nodeRank_eq_accRank hT _ hacc]
      exact hrank

/-- Strict whole-tree rank stages are monotone in their ordinal bound.-/
theorem treeRankLT_mono {i j : Ordinal.{0}} (hij : i ≤ j) :
    treeRankLT i ⊆ treeRankLT j := by
  rintro c ⟨hT, hrank⟩
  exact ⟨hT, hrank.trans_le hij⟩

/-- Ill-founded decoded trees belong to no strict whole-tree rank stage.-/
theorem not_mem_treeRankLT_of_not_isWellFounded {i : Ordinal.{0}} {c : TreeCode}
    (hc : ¬IsWellFounded (decodeTree c)) : c ∉ treeRankLT i := by
  rintro ⟨hT, -⟩
  exact hc hT

/-- Exact whole-tree successor equation in terms of root membership and child stages.-/
theorem treeRankLT_succ (i : Ordinal.{0}) :
    treeRankLT (Order.succ i) =
      {c | [] ∉ decodeTree c} ∪
        ({c | [] ∈ decodeTree c} ∩
          ⋂ a : ℕ, ({c | [a] ∉ decodeTree c} ∪ nodeRankLT i [a])) := by
  rw [treeRankLT_eq_root (bot_le.trans_lt (Order.lt_succ i)), nodeRankLT_succ]
  rfl

/-- At a nonzero limit, a whole-tree stage is the union of all earlier stages.-/
theorem treeRankLT_limit {i : Ordinal.{0}} (hi : Order.IsSuccLimit i) :
    treeRankLT i = ⋃ j : Set.Iio i, treeRankLT j.1 := by
  ext c
  constructor
  · rintro ⟨hT, hrank⟩
    refine Set.mem_iUnion.2 ⟨⟨Order.succ (rank (decodeTree c) hT), hi.succ_lt hrank⟩, ?_⟩
    exact ⟨hT, Order.lt_succ _⟩
  · intro hc
    rcases Set.mem_iUnion.1 hc with ⟨j, hT, hrank⟩
    exact ⟨hT, hrank.trans j.property⟩

/-- Every countable strict whole-tree rank stage is Borel measurable.-/
theorem borelMeasurableSet_treeRankLT {i : Ordinal.{0}} (hi : IsCountableBorelLevel i) :
    @MeasurableSet TreeCode (borel TreeCode) (treeRankLT i) := by
  by_cases hi0 : i = 0
  · subst i
    simp
  · rw [treeRankLT_eq_root (pos_iff_ne_zero.mpr hi0)]
    have hroot : @MeasurableSet TreeCode (borel TreeCode)
        {c | [] ∈ decodeTree c} :=
      MeasurableSpace.GenerateMeasurable.basic _ (isClopen_nodeMem []).isOpen
    exact hroot.compl.union (borelMeasurableSet_nodeRankLT hi [])

/-- Every countable strict whole-tree rank stage has an exact Borel-code witness.-/
theorem exists_borelCode_treeRankLT {i : Ordinal.{0}} (hi : IsCountableBorelLevel i) :
    ∃ c : BorelCode TreeCode, c.eval = treeRankLT i :=
  BorelCode.borelMeasurableSet_iff_exists_code.mp (borelMeasurableSet_treeRankLT hi)

end DescriptiveSetTheory.Tree
