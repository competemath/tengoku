/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Complexity
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.RankStages
import Tengoku.Seed.Logic.Equiv.Nat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic and coanalytic comparisons for the well-founded-tree rank

A Boolean code describes a simulation between nodes of two coded trees. Every source child of a
related pair must have some related target child. Existence of a simulation is analytic, and on a
well-founded target it is equivalent to the expected ordinal-rank comparison. A strict comparison
uses a simulation from the source root into one child of the target root.

The analytic comparison relations are completed by declaring every ill-founded target larger than
every tree. Their reversed-complement companions are coanalytic. When the second input is
well-founded, both polarities agree exactly with membership of the first input in `wellFoundedTrees`
and comparison of the two ordinal ranks. The coanalytic companions also have the standard global
`∞`-extension truth table: an ill-founded first input is never below anything, while a
well-founded first input is below every ill-founded second input.
-/

open Ordinal Set

namespace DescriptiveSetTheory.Tree

/-- A Boolean code for a binary relation on finite natural-number sequences.-/
abbrev NodeRelationCode := List ℕ → Bool

/-- A fixed coding of pairs of finite nodes by one finite node.-/
private def nodePairEquiv : (List ℕ × List ℕ) ≃ List ℕ :=
  Equiv.prodEquivOfEquivNat Equiv.listNatEquivNat

/-- Whether a Boolean relation code relates two finite nodes.-/
def NodeRelationCode.Relates (r : NodeRelationCode) (s t : List ℕ) : Prop :=
  r (nodePairEquiv (s, t)) = true

/-- The local child-simulation condition between two coded trees.-/
def IsRankSimulation (S T : TreeCode) (r : NodeRelationCode) : Prop :=
  ∀ (s t : List ℕ) (a : ℕ), r.Relates s t → s ++ [a] ∈ decodeTree S →
    ∃ b : ℕ, t ++ [b] ∈ decodeTree T ∧ r.Relates (s ++ [a]) (t ++ [b])

/-- Coded simulations anchored at a specified pair of finite nodes.-/
def rankSimulationWitnesses (s t : List ℕ) :
    Set ((TreeCode × TreeCode) × NodeRelationCode) :=
  {p | p.2.Relates s t ∧ IsRankSimulation p.1.1 p.1.2 p.2}

/-- Existence of a coded simulation anchored at `s` and `t`.-/
def rankSimulationFrom (s t : List ℕ) : Set (TreeCode × TreeCode) :=
  {p | ∃ r : NodeRelationCode, r.Relates s t ∧ IsRankSimulation p.1 p.2 r}

/-- The non-strict raw simulation comparison, anchored at the two roots.-/
def treeRankLeSimulation : Set (TreeCode × TreeCode) :=
  rankSimulationFrom [] []

/-- The strict raw simulation comparison, anchored at the source root and a target-root child.-/
def treeRankLtSimulation : Set (TreeCode × TreeCode) :=
  {p | ∃ b : ℕ, [b] ∈ decodeTree p.2 ∧ p ∈ rankSimulationFrom [] [b]}

private theorem isClopen_relationCoordinate (s t : List ℕ) :
    IsClopen {p : (TreeCode × TreeCode) × NodeRelationCode | p.2.Relates s t} := by
  have hcontinuous : Continuous (fun p : (TreeCode × TreeCode) × NodeRelationCode =>
      p.2 (nodePairEquiv (s, t))) :=
    (continuous_listNatBoolCoordinate (nodePairEquiv (s, t))).comp continuous_snd
  simpa [NodeRelationCode.Relates, Set.preimage, Set.mem_singleton_iff] using
    (isClopen_discrete ({true} : Set Bool)).preimage hcontinuous

private theorem isClopen_sourceCoordinate (s : List ℕ) :
    IsClopen {p : (TreeCode × TreeCode) × NodeRelationCode | s ∈ decodeTree p.1.1} := by
  have hcontinuous : Continuous (fun p : (TreeCode × TreeCode) × NodeRelationCode =>
      p.1.1.1 s) :=
    ((continuous_listNatBoolCoordinate s).comp continuous_subtype_val).comp
      (continuous_fst.comp continuous_fst)
  simpa [Set.preimage, Set.mem_singleton_iff] using
    (isClopen_discrete ({true} : Set Bool)).preimage hcontinuous

private theorem isClopen_targetCoordinate (t : List ℕ) :
    IsClopen {p : (TreeCode × TreeCode) × NodeRelationCode | t ∈ decodeTree p.1.2} := by
  have hcontinuous : Continuous (fun p : (TreeCode × TreeCode) × NodeRelationCode =>
      p.1.2.1 t) :=
    ((continuous_listNatBoolCoordinate t).comp continuous_subtype_val).comp
      (continuous_snd.comp continuous_fst)
  simpa [Set.preimage, Set.mem_singleton_iff] using
    (isClopen_discrete ({true} : Set Bool)).preimage hcontinuous

/-- The set of anchored simulation witnesses is Borel measurable.-/
theorem measurableSet_rankSimulationWitnesses (s₀ t₀ : List ℕ) :
    MeasurableSet (rankSimulationWitnesses s₀ t₀) := by
  rw [show rankSimulationWitnesses s₀ t₀ =
      {p | p.2.Relates s₀ t₀} ∩
        ⋂ s : List ℕ, ⋂ t : List ℕ, ⋂ a : ℕ,
          ({p | p.2.Relates s t} ∩
            {p | s ++ [a] ∈ decodeTree p.1.1})ᶜ ∪
              ⋃ b : ℕ, ({p | t ++ [b] ∈ decodeTree p.1.2} ∩
                {p | p.2.Relates (s ++ [a]) (t ++ [b])}) by
    ext p
    simp only [rankSimulationWitnesses, IsRankSimulation, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Set.mem_iUnion, not_and_or]
    constructor
    · rintro ⟨hroot, hsim⟩
      refine ⟨hroot, fun s t a => ?_⟩
      by_cases hrel : p.2.Relates s t
      · by_cases hsource : s ++ [a] ∈ decodeTree p.1.1
        · exact Or.inr (hsim s t a hrel hsource)
        · exact Or.inl (Or.inr hsource)
      · exact Or.inl (Or.inl hrel)
    · rintro ⟨hroot, hall⟩
      refine ⟨hroot, fun s t a hrel hsource => ?_⟩
      rcases hall s t a with (hmissing | hexists)
      · rcases hmissing with hmissing | hmissing
        · exact (hmissing hrel).elim
        · exact (hmissing hsource).elim
      · exact hexists]
  refine (isClopen_relationCoordinate s₀ t₀).isOpen.measurableSet.inter
    (MeasurableSet.iInter fun s => MeasurableSet.iInter fun t =>
      MeasurableSet.iInter fun a => ?_)
  exact ((isClopen_relationCoordinate s t).isOpen.measurableSet.inter
      (isClopen_sourceCoordinate (s ++ [a])).isOpen.measurableSet).compl.union
    (MeasurableSet.iUnion fun b =>
      (isClopen_targetCoordinate (t ++ [b])).isOpen.measurableSet.inter
        (isClopen_relationCoordinate (s ++ [a]) (t ++ [b])).isOpen.measurableSet)

/-- Existence of an anchored rank simulation is analytic.-/
theorem analyticSet_rankSimulationFrom (s t : List ℕ) :
    MeasureTheory.AnalyticSet (rankSimulationFrom s t) := by
  rw [show rankSimulationFrom s t = Prod.fst '' rankSimulationWitnesses s t by
    ext p
    constructor
    · rintro ⟨r, hr, hsim⟩
      exact ⟨(p, r), ⟨hr, hsim⟩, rfl⟩
    · rintro ⟨⟨q, r⟩, ⟨hr, hsim⟩, hq⟩
      change q = p at hq
      subst q
      exact ⟨r, hr, hsim⟩]
  exact (measurableSet_rankSimulationWitnesses s t).analyticSet.image_of_continuous
    continuous_fst

/-- The raw non-strict tree-rank simulation relation is analytic.-/
theorem analyticSet_treeRankLeSimulation :
    MeasureTheory.AnalyticSet treeRankLeSimulation :=
  analyticSet_rankSimulationFrom [] []

/-- The raw strict tree-rank simulation relation is analytic.-/
theorem analyticSet_treeRankLtSimulation :
    MeasureTheory.AnalyticSet treeRankLtSimulation := by
  rw [show treeRankLtSimulation = ⋃ b : ℕ,
      Prod.fst ''
        (rankSimulationWitnesses [] [b] ∩
          {p : (TreeCode × TreeCode) × NodeRelationCode |
            [b] ∈ decodeTree p.1.2}) by
    ext p
    simp only [treeRankLtSimulation, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨b, hb, r, hr, hsim⟩
      exact ⟨b, (p, r), ⟨⟨hr, hsim⟩, hb⟩, rfl⟩
    · rintro ⟨b, ⟨q, r⟩, ⟨⟨hr, hsim⟩, hb⟩, hq⟩
      change q = p at hq
      subst q
      exact ⟨b, hb, r, hr, hsim⟩]
  exact MeasureTheory.AnalyticSet.iUnion fun b =>
    ((measurableSet_rankSimulationWitnesses [] [b]).inter
      (isClopen_targetCoordinate [b]).isOpen.measurableSet).analyticSet.image_of_continuous
        continuous_fst

private noncomputable def rankAt (T : Descriptive.tree ℕ) (hT : IsWellFounded T)
    (s : List ℕ) : Ordinal.{0} := by
  classical
  exact if hs : s ∈ T then nodeRank hT ⟨s, hs⟩ else 0

private theorem rankAt_eq_nodeRank {T : Descriptive.tree ℕ} (hT : IsWellFounded T)
    {s : List ℕ} (hs : s ∈ T) :
    rankAt T hT s = nodeRank hT ⟨s, hs⟩ := by
  simp [rankAt, hs]

private theorem rankAt_eq_zero {T : Descriptive.tree ℕ} (hT : IsWellFounded T)
    {s : List ℕ} (hs : s ∉ T) : rankAt T hT s = 0 := by
  simp [rankAt, hs]

private theorem rankAt_nil_eq_rank {T : Descriptive.tree ℕ} (hT : IsWellFounded T) :
    rankAt T hT [] = rank T hT := by
  by_cases hroot : [] ∈ T
  · rw [rankAt_eq_nodeRank hT hroot, rank_eq_nodeRank hT hroot]
  · rw [rankAt_eq_zero hT hroot, rank_eq_zero_of_nil_not_mem hT hroot]

private theorem nodeRank_eq_accRank {T : Descriptive.tree ℕ} (hT : IsWellFounded T)
    (s : T) (hacc : Acc (Child T) s) : nodeRank hT s = hacc.rank := by
  letI : _root_.IsWellFounded T (Child T) := ⟨hT⟩
  unfold nodeRank _root_.IsWellFounded.rank
  rw [Subsingleton.elim (_root_.IsWellFounded.apply (Child T) s) hacc]

private theorem exists_acc_rank_le_of_simulation {S T : TreeCode} {r : NodeRelationCode}
    (hsim : IsRankSimulation S T r) {source : decodeTree S} {target : decodeTree T}
    (hrel : r.Relates source.1 target.1)
    (haccT : Acc (Child (decodeTree T)) target) :
    ∃ haccS : Acc (Child (decodeTree S)) source,
      haccS.rank ≤ haccT.rank := by
  induction haccT generalizing source with
  | intro target hbelow ih =>
      have hmatch (sourceChild : decodeTree S)
          (hsourceChild : Child (decodeTree S) sourceChild source) :
          ∃ targetChild : decodeTree T,
            Child (decodeTree T) targetChild target ∧
              r.Relates sourceChild.1 targetChild.1 := by
        obtain ⟨a, ha⟩ := hsourceChild
        have hsourceMem : source.1 ++ [a] ∈ decodeTree S := by
          rw [← ha]
          exact sourceChild.2
        obtain ⟨b, htargetMem, hchildRel⟩ :=
          hsim source.1 target.1 a hrel hsourceMem
        let targetChild : decodeTree T := ⟨target.1 ++ [b], htargetMem⟩
        refine ⟨targetChild, ⟨b, rfl⟩, ?_⟩
        simpa [targetChild, ha] using hchildRel
      let haccS : Acc (Child (decodeTree S)) source :=
        Acc.intro _ fun sourceChild hsourceChild => by
          obtain ⟨targetChild, htargetChild, hchildRel⟩ :=
            hmatch sourceChild hsourceChild
          exact (ih targetChild htargetChild hchildRel).choose
      refine ⟨haccS, ?_⟩
      rw [haccS.rank_eq]
      refine Ordinal.iSup_le fun sourceChild => ?_
      obtain ⟨targetChild, htargetChild, hchildRel⟩ :=
        hmatch sourceChild.1 sourceChild.2
      obtain ⟨haccSource, hrank⟩ :=
        ih targetChild htargetChild hchildRel
      have hsourceRank : (haccS.inv sourceChild.2).rank = haccSource.rank :=
        congrArg Acc.rank (Subsingleton.elim _ _)
      calc
        Order.succ (haccS.inv sourceChild.2).rank = Order.succ haccSource.rank :=
          congrArg Order.succ hsourceRank
        _ ≤ Order.succ (hbelow targetChild htargetChild).rank :=
          Order.succ_le_succ hrank
        _ ≤ (Acc.intro target hbelow).rank := by
          rw [(Acc.intro target hbelow).rank_eq]
          exact Ordinal.le_iSup
            (fun child : {child : decodeTree T // Child (decodeTree T) child target} =>
              Order.succ ((Acc.intro target hbelow).inv child.2).rank)
            ⟨targetChild, htargetChild⟩

private noncomputable def ordinalComparisonCode (S T : TreeCode)
    (hS : IsWellFounded (decodeTree S)) (hT : IsWellFounded (decodeTree T)) :
    NodeRelationCode := fun n =>
  decide (rankAt (decodeTree S) hS (nodePairEquiv.symm n).1 ≤
    rankAt (decodeTree T) hT (nodePairEquiv.symm n).2)

private theorem ordinalComparisonCode_relates (S T : TreeCode)
    (hS : IsWellFounded (decodeTree S)) (hT : IsWellFounded (decodeTree T))
    (s t : List ℕ) :
    (ordinalComparisonCode S T hS hT).Relates s t ↔
      rankAt (decodeTree S) hS s ≤ rankAt (decodeTree T) hT t := by
  classical
  simp [NodeRelationCode.Relates, ordinalComparisonCode, nodePairEquiv]

private theorem ordinalComparisonCode_isRankSimulation (S T : TreeCode)
    (hS : IsWellFounded (decodeTree S)) (hT : IsWellFounded (decodeTree T)) :
    IsRankSimulation S T (ordinalComparisonCode S T hS hT) := by
  intro s t a hrel hsourceChild
  have hsource : s ∈ decodeTree S := (decodeTree S).property hsourceChild
  have hsourceLt :
      rankAt (decodeTree S) hS (s ++ [a]) < rankAt (decodeTree S) hS s := by
    rw [rankAt_eq_nodeRank hS hsourceChild, rankAt_eq_nodeRank hS hsource]
    exact nodeRank_lt_of_child hS ⟨a, rfl⟩
  have hle := (ordinalComparisonCode_relates S T hS hT s t).mp hrel
  have hsourceTargetLt :
      rankAt (decodeTree S) hS (s ++ [a]) < rankAt (decodeTree T) hT t :=
    hsourceLt.trans_le hle
  by_cases htarget : t ∈ decodeTree T
  · rw [rankAt_eq_nodeRank hS hsourceChild, rankAt_eq_nodeRank hT htarget,
      nodeRank_eq hT] at hsourceTargetLt
    rw [Ordinal.lt_iSup_iff] at hsourceTargetLt
    obtain ⟨targetChild, htargetChildRank⟩ := hsourceTargetLt
    obtain ⟨b, hb⟩ := targetChild.2
    have htargetChildMem : t ++ [b] ∈ decodeTree T := by
      rw [← hb]
      exact targetChild.1.2
    refine ⟨b, htargetChildMem, ?_⟩
    rw [ordinalComparisonCode_relates]
    rw [rankAt_eq_nodeRank hS hsourceChild, rankAt_eq_nodeRank hT htargetChildMem]
    rw [Order.lt_succ_iff] at htargetChildRank
    have htargetEq : targetChild.1 =
        (⟨t ++ [b], htargetChildMem⟩ : decodeTree T) := Subtype.ext hb
    simpa [htargetEq] using htargetChildRank
  · rw [rankAt_eq_zero hT htarget] at hsourceTargetLt
    exact (not_lt_zero hsourceTargetLt).elim

private theorem rankSimulationFrom_iff_rankAt_le {S T : TreeCode}
    (hS : IsWellFounded (decodeTree S)) (hT : IsWellFounded (decodeTree T))
    (s t : List ℕ) :
    (S, T) ∈ rankSimulationFrom s t ↔
      rankAt (decodeTree S) hS s ≤ rankAt (decodeTree T) hT t := by
  constructor
  · rintro ⟨r, hrel, hsim⟩
    by_cases hsource : s ∈ decodeTree S
    · by_cases htarget : t ∈ decodeTree T
      · have haccT : Acc (Child (decodeTree T))
            (⟨t, htarget⟩ : decodeTree T) :=
          (show WellFounded (Child (decodeTree T)) from hT).apply _
        obtain ⟨haccS, hrank⟩ :=
          exists_acc_rank_le_of_simulation
            (source := (⟨s, hsource⟩ : decodeTree S))
            (target := (⟨t, htarget⟩ : decodeTree T)) hsim (by simpa using hrel) haccT
        rw [rankAt_eq_nodeRank hS hsource, rankAt_eq_nodeRank hT htarget]
        calc
          nodeRank hS ⟨s, hsource⟩ = haccS.rank :=
            nodeRank_eq_accRank hS _ haccS
          _ ≤ haccT.rank := hrank
          _ = nodeRank hT ⟨t, htarget⟩ :=
            (nodeRank_eq_accRank hT _ haccT).symm
      · rw [rankAt_eq_nodeRank hS hsource, rankAt_eq_zero hT htarget,
          nodeRank_eq hS]
        refine Ordinal.iSup_le fun sourceChild => ?_
        obtain ⟨a, ha⟩ := sourceChild.2
        have hsourceChild : s ++ [a] ∈ decodeTree S := by
          rw [← ha]
          exact sourceChild.1.2
        obtain ⟨b, htargetChild, -⟩ := hsim s t a hrel hsourceChild
        exact (htarget ((decodeTree T).property htargetChild)).elim
    · rw [rankAt_eq_zero hS hsource]
      exact bot_le
  · intro hrank
    refine ⟨ordinalComparisonCode S T hS hT, ?_,
      ordinalComparisonCode_isRankSimulation S T hS hT⟩
    exact (ordinalComparisonCode_relates S T hS hT s t).2 hrank

private theorem isWellFounded_of_root_simulation_to_node {S T : TreeCode}
    {r : NodeRelationCode} {t : List ℕ} (htarget : t ∈ decodeTree T)
    (hT : IsWellFounded (decodeTree T)) (hrel : r.Relates [] t)
    (hsim : IsRankSimulation S T r) : IsWellFounded (decodeTree S) := by
  by_cases hsource : [] ∈ decodeTree S
  · have haccT : Acc (Child (decodeTree T))
        (⟨t, htarget⟩ : decodeTree T) :=
      (show WellFounded (Child (decodeTree T)) from hT).apply _
    obtain ⟨haccS, -⟩ :=
      exists_acc_rank_le_of_simulation
        (source := (⟨[], hsource⟩ : decodeTree S))
        (target := (⟨t, htarget⟩ : decodeTree T)) hsim (by simpa using hrel) haccT
    exact (acc_root_iff_isWellFounded hsource).1 haccS
  · have hbot : decodeTree S = ⊥ := Descriptive.Tree.tree_eq_bot.mpr hsource
    rw [hbot]
    exact isWellFounded_iff_body_eq_empty.mpr body_bot

/-- On a well-founded target, raw non-strict simulation is exactly non-strict tree-rank
comparison, and it forces the source tree to be well-founded.-/
theorem mem_treeRankLeSimulation_iff {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLeSimulation ↔
      ∃ hS : IsWellFounded (decodeTree S),
        rank (decodeTree S) hS ≤ rank (decodeTree T) hT := by
  constructor
  · intro hsimulation
    rcases hsimulation with ⟨r, hrootRel, hsim⟩
    have hS : IsWellFounded (decodeTree S) := by
      by_cases htarget : [] ∈ decodeTree T
      · exact isWellFounded_of_root_simulation_to_node htarget hT hrootRel hsim
      · by_cases hsource : [] ∈ decodeTree S
        · have haccS : Acc (Child (decodeTree S))
              (⟨[], hsource⟩ : decodeTree S) :=
            Acc.intro _ fun sourceChild hsourceChild => by
              obtain ⟨a, ha⟩ := hsourceChild
              have ha' : sourceChild.1 = [a] := by simpa using ha
              have hsourceChildMem : [a] ∈ decodeTree S := by
                rw [← ha']
                exact sourceChild.2
              obtain ⟨b, htargetChild, -⟩ :=
                hsim [] [] a hrootRel hsourceChildMem
              exact (htarget ((decodeTree T).property htargetChild)).elim
          exact (acc_root_iff_isWellFounded hsource).1 haccS
        · have hbot : decodeTree S = ⊥ := Descriptive.Tree.tree_eq_bot.mpr hsource
          rw [hbot]
          exact isWellFounded_iff_body_eq_empty.mpr body_bot
    refine ⟨hS, ?_⟩
    have hrank := (rankSimulationFrom_iff_rankAt_le hS hT [] []).1
      ⟨r, hrootRel, hsim⟩
    simpa only [rankAt_nil_eq_rank] using hrank
  · rintro ⟨hS, hrank⟩
    apply (rankSimulationFrom_iff_rankAt_le hS hT [] []).2
    simpa only [rankAt_nil_eq_rank] using hrank

/-- On a well-founded target, raw strict simulation is exactly strict tree-rank comparison, and
it forces the source tree to be well-founded.-/
theorem mem_treeRankLtSimulation_iff {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLtSimulation ↔
      ∃ hS : IsWellFounded (decodeTree S),
        rank (decodeTree S) hS < rank (decodeTree T) hT := by
  constructor
  · rintro ⟨b, htargetChild, hsimulation⟩
    rcases hsimulation with ⟨r, hrootChildRel, hsim⟩
    have hS : IsWellFounded (decodeTree S) :=
      isWellFounded_of_root_simulation_to_node htargetChild hT hrootChildRel hsim
    refine ⟨hS, ?_⟩
    have hle := (rankSimulationFrom_iff_rankAt_le hS hT [] [b]).1
      ⟨r, hrootChildRel, hsim⟩
    have htargetRoot : [] ∈ decodeTree T := (decodeTree T).property htargetChild
    rw [rankAt_nil_eq_rank, rankAt_eq_nodeRank hT htargetChild] at hle
    rw [rank_eq_nodeRank hT htargetRoot]
    exact hle.trans_lt (nodeRank_lt_of_child hT ⟨b, rfl⟩)
  · rintro ⟨hS, hrank⟩
    by_cases htargetRoot : [] ∈ decodeTree T
    · rw [rank_eq_nodeRank hT htargetRoot, nodeRank_eq hT,
        Ordinal.lt_iSup_iff] at hrank
      obtain ⟨targetChild, htargetChildRank⟩ := hrank
      rw [Order.lt_succ_iff] at htargetChildRank
      obtain ⟨b, hb⟩ := targetChild.2
      have hb' : targetChild.1.1 = [b] := by simpa using hb
      have htargetChild : [b] ∈ decodeTree T := by
        rw [← hb']
        exact targetChild.1.2
      refine ⟨b, htargetChild, ?_⟩
      apply (rankSimulationFrom_iff_rankAt_le hS hT [] [b]).2
      rw [rankAt_nil_eq_rank, rankAt_eq_nodeRank hT htargetChild]
      have htargetEq : targetChild.1 =
          (⟨[b], htargetChild⟩ : decodeTree T) := Subtype.ext hb'
      simpa [htargetEq] using htargetChildRank
    · rw [rank_eq_zero_of_nil_not_mem hT htargetRoot] at hrank
      exact (not_lt_zero hrank).elim

private theorem analyticSet_union {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : MeasureTheory.AnalyticSet s) (ht : MeasureTheory.AnalyticSet t) :
    MeasureTheory.AnalyticSet (s ∪ t) := by
  rw [show s ∪ t = ⋃ b : Bool, if b then s else t by
    ext x
    simp [or_comm]]
  exact MeasureTheory.AnalyticSet.iUnion fun b => by
    cases b <;> simp_all

/-- The analytic non-strict comparison. An ill-founded target is declared above every tree; for a
well-founded target the raw simulation supplies the exact rank comparison.-/
def treeRankLeAnalytic : Set (TreeCode × TreeCode) :=
  {p | p.2 ∈ illFoundedTrees} ∪ treeRankLeSimulation

/-- The analytic strict comparison. An ill-founded target is declared strictly above every tree;
for a well-founded target the raw root-to-child simulation supplies the exact rank comparison.-/
def treeRankLtAnalytic : Set (TreeCode × TreeCode) :=
  {p | p.2 ∈ illFoundedTrees} ∪ treeRankLtSimulation

/-- The coanalytic non-strict comparison, defined as the reversed strict simulation complement
after excluding every ill-founded source.-/
def treeRankLeCoanalytic : Set (TreeCode × TreeCode) :=
  ({p | p.1 ∈ illFoundedTrees} ∪
    {p | (p.2, p.1) ∈ treeRankLtSimulation})ᶜ

/-- The coanalytic strict comparison, defined as the reversed non-strict simulation complement
after excluding every ill-founded source.-/
def treeRankLtCoanalytic : Set (TreeCode × TreeCode) :=
  ({p | p.1 ∈ illFoundedTrees} ∪
    {p | (p.2, p.1) ∈ treeRankLeSimulation})ᶜ

private theorem analyticSet_targetIllFounded :
    MeasureTheory.AnalyticSet {p : TreeCode × TreeCode | p.2 ∈ illFoundedTrees} := by
  simpa [Set.preimage] using
    analyticSet_illFoundedTrees.preimage (X := TreeCode × TreeCode) continuous_snd

private theorem analyticSet_sourceIllFounded :
    MeasureTheory.AnalyticSet {p : TreeCode × TreeCode | p.1 ∈ illFoundedTrees} := by
  simpa [Set.preimage] using
    analyticSet_illFoundedTrees.preimage (X := TreeCode × TreeCode) continuous_fst

private theorem analyticSet_swap_treeRankLeSimulation :
    MeasureTheory.AnalyticSet
      {p : TreeCode × TreeCode | (p.2, p.1) ∈ treeRankLeSimulation} := by
  simpa [Set.preimage] using analyticSet_treeRankLeSimulation.preimage
    (continuous_snd.prodMk continuous_fst)

private theorem analyticSet_swap_treeRankLtSimulation :
    MeasureTheory.AnalyticSet
      {p : TreeCode × TreeCode | (p.2, p.1) ∈ treeRankLtSimulation} := by
  simpa [Set.preimage] using analyticSet_treeRankLtSimulation.preimage
    (continuous_snd.prodMk continuous_fst)

/-- The completed non-strict comparison has the analytic polarity required for a coanalytic
norm.-/
theorem analyticSet_treeRankLeAnalytic :
    MeasureTheory.AnalyticSet treeRankLeAnalytic :=
  analyticSet_union analyticSet_targetIllFounded analyticSet_treeRankLeSimulation

/-- The completed strict comparison is analytic.-/
theorem analyticSet_treeRankLtAnalytic :
    MeasureTheory.AnalyticSet treeRankLtAnalytic :=
  analyticSet_union analyticSet_targetIllFounded analyticSet_treeRankLtSimulation

/-- The reversed-complement non-strict comparison is coanalytic.-/
theorem isCoanalytic_treeRankLeCoanalytic : IsCoanalytic treeRankLeCoanalytic := by
  change MeasureTheory.AnalyticSet
    (({p : TreeCode × TreeCode | p.1 ∈ illFoundedTrees} ∪
      {p | (p.2, p.1) ∈ treeRankLtSimulation})ᶜ)ᶜ
  rw [compl_compl]
  exact analyticSet_union analyticSet_sourceIllFounded analyticSet_swap_treeRankLtSimulation

/-- The reversed-complement strict comparison is coanalytic.-/
theorem isCoanalytic_treeRankLtCoanalytic : IsCoanalytic treeRankLtCoanalytic := by
  change MeasureTheory.AnalyticSet
    (({p : TreeCode × TreeCode | p.1 ∈ illFoundedTrees} ∪
      {p | (p.2, p.1) ∈ treeRankLeSimulation})ᶜ)ᶜ
  rw [compl_compl]
  exact analyticSet_union analyticSet_sourceIllFounded analyticSet_swap_treeRankLeSimulation

/-- Full well-founded/ill-founded truth table for the analytic non-strict comparison. An
ill-founded target makes the relation true regardless of the source; otherwise both trees are
well-founded and their ranks are compared.-/
theorem mem_treeRankLeAnalytic_iff {S T : TreeCode} :
    (S, T) ∈ treeRankLeAnalytic ↔
      ¬IsWellFounded (decodeTree T) ∨
        ∃ hT : IsWellFounded (decodeTree T),
          ∃ hS : IsWellFounded (decodeTree S),
            rank (decodeTree S) hS ≤ rank (decodeTree T) hT := by
  constructor
  · rintro (htarget | hsimulation)
    · exact Or.inl htarget
    · by_cases hT : IsWellFounded (decodeTree T)
      · exact Or.inr ⟨hT, (mem_treeRankLeSimulation_iff hT).1 hsimulation⟩
      · exact Or.inl hT
  · rintro (hT | ⟨hT, hS, hrank⟩)
    · exact Or.inl hT
    · exact Or.inr ((mem_treeRankLeSimulation_iff hT).2 ⟨hS, hrank⟩)

/-- Full well-founded/ill-founded truth table for the analytic strict comparison.-/
theorem mem_treeRankLtAnalytic_iff {S T : TreeCode} :
    (S, T) ∈ treeRankLtAnalytic ↔
      ¬IsWellFounded (decodeTree T) ∨
        ∃ hT : IsWellFounded (decodeTree T),
          ∃ hS : IsWellFounded (decodeTree S),
            rank (decodeTree S) hS < rank (decodeTree T) hT := by
  constructor
  · rintro (htarget | hsimulation)
    · exact Or.inl htarget
    · by_cases hT : IsWellFounded (decodeTree T)
      · exact Or.inr ⟨hT, (mem_treeRankLtSimulation_iff hT).1 hsimulation⟩
      · exact Or.inl hT
  · rintro (hT | ⟨hT, hS, hrank⟩)
    · exact Or.inl hT
    · exact Or.inr ((mem_treeRankLtSimulation_iff hT).2 ⟨hS, hrank⟩)

/-- Full truth table for the coanalytic non-strict comparison. It is the standard extension of
the well-founded-tree rank obtained by assigning rank `∞` outside `wellFoundedTrees`.-/
theorem mem_treeRankLeCoanalytic_iff {S T : TreeCode} :
    (S, T) ∈ treeRankLeCoanalytic ↔
      ∃ hS : IsWellFounded (decodeTree S),
        ¬IsWellFounded (decodeTree T) ∨
          ∃ hT : IsWellFounded (decodeTree T),
            rank (decodeTree S) hS ≤ rank (decodeTree T) hT := by
  constructor
  · intro hcomparison
    change ¬(S ∈ illFoundedTrees ∨ (T, S) ∈ treeRankLtSimulation) at hcomparison
    have hS : IsWellFounded (decodeTree S) := by
      by_contra hS
      exact hcomparison (Or.inl hS)
    refine ⟨hS, ?_⟩
    by_cases hT : IsWellFounded (decodeTree T)
    · refine Or.inr ⟨hT, ?_⟩
      have hnotLt : ¬rank (decodeTree T) hT < rank (decodeTree S) hS := by
        intro hrank
        exact hcomparison (Or.inr ((mem_treeRankLtSimulation_iff hS).2 ⟨hT, hrank⟩))
      exact not_lt.mp hnotLt
    · exact Or.inl hT
  · rintro ⟨hS, htarget⟩
    change ¬(S ∈ illFoundedTrees ∨ (T, S) ∈ treeRankLtSimulation)
    rintro (hsource | hcomparison)
    · exact hsource hS
    · obtain ⟨hT, hrank⟩ := (mem_treeRankLtSimulation_iff hS).1 hcomparison
      rcases htarget with htarget | ⟨hT', hle⟩
      · exact htarget hT
      · have hp : hT = hT' := Subsingleton.elim _ _
        subst hT
        exact (not_lt_of_ge hle hrank)

/-- Full truth table for the coanalytic strict comparison, again using the standard `∞`
extension outside the domain.-/
theorem mem_treeRankLtCoanalytic_iff {S T : TreeCode} :
    (S, T) ∈ treeRankLtCoanalytic ↔
      ∃ hS : IsWellFounded (decodeTree S),
        ¬IsWellFounded (decodeTree T) ∨
          ∃ hT : IsWellFounded (decodeTree T),
            rank (decodeTree S) hS < rank (decodeTree T) hT := by
  constructor
  · intro hcomparison
    change ¬(S ∈ illFoundedTrees ∨ (T, S) ∈ treeRankLeSimulation) at hcomparison
    have hS : IsWellFounded (decodeTree S) := by
      by_contra hS
      exact hcomparison (Or.inl hS)
    refine ⟨hS, ?_⟩
    by_cases hT : IsWellFounded (decodeTree T)
    · refine Or.inr ⟨hT, ?_⟩
      have hnotLe : ¬rank (decodeTree T) hT ≤ rank (decodeTree S) hS := by
        intro hrank
        exact hcomparison (Or.inr ((mem_treeRankLeSimulation_iff hS).2 ⟨hT, hrank⟩))
      exact lt_of_not_ge hnotLe
    · exact Or.inl hT
  · rintro ⟨hS, htarget⟩
    change ¬(S ∈ illFoundedTrees ∨ (T, S) ∈ treeRankLeSimulation)
    rintro (hsource | hcomparison)
    · exact hsource hS
    · obtain ⟨hT, hrank⟩ := (mem_treeRankLeSimulation_iff hS).1 hcomparison
      rcases htarget with htarget | ⟨hT', hlt⟩
      · exact htarget hT
      · have hp : hT = hT' := Subsingleton.elim _ _
        subst hT
        exact (not_le_of_gt hlt hrank)

/-- With a well-founded second input, the analytic non-strict comparison has exactly the rank
semantics required in the definition of a coanalytic norm.-/
theorem mem_treeRankLeAnalytic_iff_of_isWellFounded {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLeAnalytic ↔
      ∃ hS : IsWellFounded (decodeTree S),
        rank (decodeTree S) hS ≤ rank (decodeTree T) hT := by
  constructor
  · intro hcomparison
    rcases mem_treeRankLeAnalytic_iff.mp hcomparison with hnot | ⟨hT', hresult⟩
    · exact (hnot hT).elim
    · have hp : hT' = hT := Subsingleton.elim _ _
      subst hT'
      exact hresult
  · intro hresult
    exact mem_treeRankLeAnalytic_iff.mpr (Or.inr ⟨hT, hresult⟩)

/-- With a well-founded second input, the analytic strict comparison is exact.-/
theorem mem_treeRankLtAnalytic_iff_of_isWellFounded {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLtAnalytic ↔
      ∃ hS : IsWellFounded (decodeTree S),
        rank (decodeTree S) hS < rank (decodeTree T) hT := by
  constructor
  · intro hcomparison
    rcases mem_treeRankLtAnalytic_iff.mp hcomparison with hnot | ⟨hT', hresult⟩
    · exact (hnot hT).elim
    · have hp : hT' = hT := Subsingleton.elim _ _
      subst hT'
      exact hresult
  · intro hresult
    exact mem_treeRankLtAnalytic_iff.mpr (Or.inr ⟨hT, hresult⟩)

/-- With a well-founded second input, the coanalytic non-strict comparison is exact.-/
theorem mem_treeRankLeCoanalytic_iff_of_isWellFounded {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLeCoanalytic ↔
      ∃ hS : IsWellFounded (decodeTree S),
        rank (decodeTree S) hS ≤ rank (decodeTree T) hT := by
  constructor
  · intro hcomparison
    obtain ⟨hS, hnot | ⟨hT', hrank⟩⟩ :=
      mem_treeRankLeCoanalytic_iff.mp hcomparison
    · exact (hnot hT).elim
    · have hp : hT' = hT := Subsingleton.elim _ _
      subst hT'
      exact ⟨hS, hrank⟩
  · rintro ⟨hS, hrank⟩
    exact mem_treeRankLeCoanalytic_iff.mpr ⟨hS, Or.inr ⟨hT, hrank⟩⟩

/-- With a well-founded second input, the coanalytic strict comparison is exact.-/
theorem mem_treeRankLtCoanalytic_iff_of_isWellFounded {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLtCoanalytic ↔
      ∃ hS : IsWellFounded (decodeTree S),
        rank (decodeTree S) hS < rank (decodeTree T) hT := by
  constructor
  · intro hcomparison
    obtain ⟨hS, hnot | ⟨hT', hrank⟩⟩ :=
      mem_treeRankLtCoanalytic_iff.mp hcomparison
    · exact (hnot hT).elim
    · have hp : hT' = hT := Subsingleton.elim _ _
      subst hT'
      exact ⟨hS, hrank⟩
  · rintro ⟨hS, hrank⟩
    exact mem_treeRankLtCoanalytic_iff.mpr ⟨hS, Or.inr ⟨hT, hrank⟩⟩

/-- The analytic and coanalytic non-strict polarities agree whenever the second input is in the
coanalytic domain of well-founded trees.-/
theorem treeRankLe_polarities_agree {S T : TreeCode}
    (hT : IsWellFounded (decodeTree T)) :
    (S, T) ∈ treeRankLeAnalytic ↔ (S, T) ∈ treeRankLeCoanalytic := by
  rw [mem_treeRankLeAnalytic_iff_of_isWellFounded hT,
    mem_treeRankLeCoanalytic_iff_of_isWellFounded hT]

/-- A strict rank stage at a realized rank is the corresponding analytic strict-comparison
section.-/
theorem treeRankLT_eq_treeRankLtAnalytic_section (T : TreeCode)
    (hT : IsWellFounded (decodeTree T)) :
    treeRankLT (rank (decodeTree T) hT) =
      {S | (S, T) ∈ treeRankLtAnalytic} := by
  ext S
  exact mem_treeRankLtAnalytic_iff_of_isWellFounded hT |>.symm

/-- The successor stage of a realized rank is the analytic non-strict-comparison section.-/
theorem treeRankLT_succ_eq_treeRankLeAnalytic_section (T : TreeCode)
    (hT : IsWellFounded (decodeTree T)) :
    treeRankLT (Order.succ (rank (decodeTree T) hT)) =
      {S | (S, T) ∈ treeRankLeAnalytic} := by
  ext S
  rw [mem_treeRankLT_succ_iff_le]
  change (∃ hS : IsWellFounded (decodeTree S),
      rank (decodeTree S) hS ≤ rank (decodeTree T) hT) ↔
    (S, T) ∈ treeRankLeAnalytic
  exact (mem_treeRankLeAnalytic_iff_of_isWellFounded hT).symm

/-- The concrete well-founded-tree rank satisfies the full definability and comparison clauses
of a coanalytic (`Π¹₁`) norm. This theorem deliberately packages the concrete result as a
proposition rather than introducing a generic public norm structure with only one consumer.-/
theorem treeRankComparison_isCoanalyticNorm :
    IsCoanalytic wellFoundedTrees ∧
      MeasureTheory.AnalyticSet treeRankLeAnalytic ∧
      IsCoanalytic treeRankLeCoanalytic ∧
      MeasureTheory.AnalyticSet treeRankLtAnalytic ∧
      IsCoanalytic treeRankLtCoanalytic ∧
      ∀ (T : TreeCode) (hT : IsWellFounded (decodeTree T)) (S : TreeCode),
        ((∃ hS : IsWellFounded (decodeTree S),
            rank (decodeTree S) hS ≤ rank (decodeTree T) hT) ↔
          (S, T) ∈ treeRankLeAnalytic) ∧
        ((∃ hS : IsWellFounded (decodeTree S),
            rank (decodeTree S) hS ≤ rank (decodeTree T) hT) ↔
          (S, T) ∈ treeRankLeCoanalytic) ∧
        ((∃ hS : IsWellFounded (decodeTree S),
            rank (decodeTree S) hS < rank (decodeTree T) hT) ↔
          (S, T) ∈ treeRankLtAnalytic) ∧
        ((∃ hS : IsWellFounded (decodeTree S),
            rank (decodeTree S) hS < rank (decodeTree T) hT) ↔
          (S, T) ∈ treeRankLtCoanalytic) := by
  refine ⟨isCoanalytic_wellFoundedTrees, analyticSet_treeRankLeAnalytic,
    isCoanalytic_treeRankLeCoanalytic, analyticSet_treeRankLtAnalytic,
    isCoanalytic_treeRankLtCoanalytic, ?_⟩
  intro T hT S
  exact ⟨(mem_treeRankLeAnalytic_iff_of_isWellFounded hT).symm,
    (mem_treeRankLeCoanalytic_iff_of_isWellFounded hT).symm,
    (mem_treeRankLtAnalytic_iff_of_isWellFounded hT).symm,
    (mem_treeRankLtCoanalytic_iff_of_isWellFounded hT).symm⟩

end DescriptiveSetTheory.Tree
