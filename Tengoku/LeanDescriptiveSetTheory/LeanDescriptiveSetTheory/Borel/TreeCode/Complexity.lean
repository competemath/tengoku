/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.TreeCode.Evaluation
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Completeness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descriptive complexity of coded-tree validity and evaluation

The local validity conditions and local Boolean evaluation equations are Borel.  Projecting a
valuation gives the analytic evaluation completion.  The opposite completion is the complement of
the corresponding false-root projection and is therefore coanalytic.  The code-validity locus is
coanalytic and complete: a continuous completion map sends a tree code to a locally coherent Borel
syntax tree which is well-founded exactly when the source tree is well-founded.
-/

open Set

universe u

namespace DescriptiveSetTheory.BorelTreeCode

variable {X : Type u}

private theorem isClopen_treeCoordinate (s : List ℕ) (value : Bool) :
    IsClopen {c : Raw | c.treeCode.1 s = value} := by
  have hcontinuous : Continuous (fun c : Raw => c.treeCode.1 s) :=
    (continuous_listNatBoolCoordinate s).comp
      (continuous_subtype_val.comp continuous_treeCode)
  simpa [Set.preimage, Set.mem_singleton_iff] using
    (isClopen_discrete ({value} : Set Bool)).preimage hcontinuous

private theorem isClopen_payloadCoordinate (s : List ℕ) (value : ℕ) :
    IsClopen {c : Raw | c.payloadAt s = value} := by
  simpa [Set.preimage, Set.mem_singleton_iff] using
    (isClopen_discrete ({value} : Set ℕ)).preimage (continuous_payloadAt s)

private theorem measurableSet_memTree (s : List ℕ) :
    MeasurableSet {c : Raw | s ∈ c.tree} := by
  simpa [Raw.mem_tree] using (isClopen_treeCoordinate s true).isOpen.measurableSet

private theorem measurableSet_notMemTree (s : List ℕ) :
    MeasurableSet {c : Raw | s ∉ c.tree} := by
  simpa [Raw.mem_tree] using (isClopen_treeCoordinate s false).isOpen.measurableSet

private theorem measurableSet_kindAt (s : List ℕ) (kind : NodeKind) :
    MeasurableSet {c : Raw | c.kindAt? s = some kind} := by
  letI : TopologicalSpace (Option NodeKind) := ⊥
  letI : DiscreteTopology (Option NodeKind) := ⟨rfl⟩
  have hcontinuousOfCode : Continuous NodeKind.ofCode? :=
    continuous_of_discreteTopology
  have hcontinuous : Continuous (fun c : Raw => c.kindAt? s) :=
    hcontinuousOfCode.comp (continuous_kindCodeAt s)
  simpa [Set.preimage, Set.mem_singleton_iff, Raw.kindAt?] using
    (isClopen_discrete ({some kind} : Set (Option NodeKind))).preimage hcontinuous
      |>.isOpen.measurableSet

private def HasLocalShape (c : Raw) (s : List ℕ) : Prop :=
  (c.kindAt? s = some .empty ∧ c.payloadAt s = 0 ∧
      ∀ n, s ++ [n] ∉ c.tree) ∨
    (c.kindAt? s = some .basic ∧ ∀ n, s ++ [n] ∉ c.tree) ∨
    (c.kindAt? s = some .compl ∧ c.payloadAt s = 0 ∧
      s ++ [0] ∈ c.tree ∧ ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree) ∨
    (c.kindAt? s = some .iUnion ∧ c.payloadAt s = 0 ∧
      ∀ n, s ++ [n] ∈ c.tree)

private theorem hasLocalShape_iff (c : Raw) (s : List ℕ) :
    HasLocalShape c s ↔ c.IsCoherentAt s ∧ c.HasExpectedChildrenAt s := by
  change HasLocalShape c s ↔
    (match c.kindAt? s with
      | some .basic => True
      | some _ => c.payloadAt s = 0
      | none => False) ∧ c.HasExpectedChildrenAt s
  cases hkind : c.kindAt? s with
  | none => simp [HasLocalShape, Raw.HasExpectedChildrenAt, hkind]
  | some kind =>
      cases kind <;> simp [HasLocalShape, Raw.HasExpectedChildrenAt, hkind]

private theorem measurableSet_hasLocalShape (s : List ℕ) :
    MeasurableSet {c : Raw | HasLocalShape c s} := by
  have hnoChildren : MeasurableSet {c : Raw | ∀ n, s ++ [n] ∉ c.tree} := by
    rw [show {c : Raw | ∀ n, s ++ [n] ∉ c.tree} =
        ⋂ n, {c | s ++ [n] ∉ c.tree} by ext; simp]
    exact MeasurableSet.iInter fun n => measurableSet_notMemTree (s ++ [n])
  have hotherChildren :
      MeasurableSet {c : Raw | ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree} := by
    rw [show {c : Raw | ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree} =
        ⋂ n, if n = 0 then Set.univ else {c | s ++ [n] ∉ c.tree} by
      ext c
      simp]
    exact MeasurableSet.iInter fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · simpa [hn] using measurableSet_notMemTree (s ++ [n])
  have hempty : MeasurableSet {c : Raw |
      c.kindAt? s = some .empty ∧ c.payloadAt s = 0 ∧
        ∀ n, s ++ [n] ∉ c.tree} :=
    (measurableSet_kindAt s .empty).inter
      ((isClopen_payloadCoordinate s 0).isOpen.measurableSet.inter hnoChildren)
  have hbasic : MeasurableSet {c : Raw |
      c.kindAt? s = some .basic ∧ ∀ n, s ++ [n] ∉ c.tree} :=
    (measurableSet_kindAt s .basic).inter hnoChildren
  have hcompl : MeasurableSet {c : Raw |
      c.kindAt? s = some .compl ∧ c.payloadAt s = 0 ∧
        s ++ [0] ∈ c.tree ∧ ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree} :=
    (measurableSet_kindAt s .compl).inter
      ((isClopen_payloadCoordinate s 0).isOpen.measurableSet.inter
        ((measurableSet_memTree (s ++ [0])).inter hotherChildren))
  have hallChildren : MeasurableSet {c : Raw | ∀ n, s ++ [n] ∈ c.tree} := by
    rw [show {c : Raw | ∀ n, s ++ [n] ∈ c.tree} =
        ⋂ n, {c | s ++ [n] ∈ c.tree} by ext; simp]
    exact MeasurableSet.iInter fun n => measurableSet_memTree (s ++ [n])
  have hiUnion : MeasurableSet {c : Raw |
      c.kindAt? s = some .iUnion ∧ c.payloadAt s = 0 ∧
        ∀ n, s ++ [n] ∈ c.tree} :=
    (measurableSet_kindAt s .iUnion).inter
      ((isClopen_payloadCoordinate s 0).isOpen.measurableSet.inter hallChildren)
  exact hempty.union (hbasic.union (hcompl.union hiUnion))

/-- The local validity locus is Borel measurable.
@isnad1 id=measurab.0h0v.s6.1e5a398773e6 from=translated src=- shape=66b19da4 vocab=4afbd636
-/
theorem measurableSet_isLocallyValid :
    MeasurableSet {c : Raw | IsLocallyValid c} := by
  rw [show {c : Raw | IsLocallyValid c} =
      {c | [] ∈ c.tree} ∩
        ⋂ s : List ℕ, {c | s ∉ c.tree} ∪ {c | HasLocalShape c s} by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union]
    change IsLocallyValid c ↔
      [] ∈ c.tree ∧ ∀ s : List ℕ, s ∉ c.tree ∨ HasLocalShape c s
    constructor
    · intro h
      refine ⟨h.root_mem, fun s => ?_⟩
      by_cases hs : s ∈ c.tree
      · exact Or.inr ((hasLocalShape_iff c s).2
          ⟨h.coherent s hs, h.expectedChildren s hs⟩)
      · exact Or.inl hs
    · rintro ⟨hroot, hall⟩
      refine ⟨hroot, ?_, ?_⟩
      · intro s hs
        rcases hall s with hnot | hshape
        · exact (hnot hs).elim
        · exact (hasLocalShape_iff c s).1 hshape |>.1
      · intro s hs
        rcases hall s with hnot | hshape
        · exact (hnot hs).elim
        · exact (hasLocalShape_iff c s).1 hshape |>.2]
  exact (measurableSet_memTree []).inter
    (MeasurableSet.iInter fun s =>
      (measurableSet_notMemTree s).union (measurableSet_hasLocalShape s))

section EvaluationComplexity

variable [MeasurableSpace X]

private theorem measurableSet_codeKindAtOnWitness (s : List ℕ) (kind : NodeKind) :
    MeasurableSet {p : ((Raw × X) × Valuation) | p.1.1.kindAt? s = some kind} :=
  (measurableSet_kindAt s kind).preimage (measurable_fst.comp measurable_fst)

private theorem measurableSet_codePayloadAtOnWitness (s : List ℕ) (value : ℕ) :
    MeasurableSet {p : ((Raw × X) × Valuation) | p.1.1.payloadAt s = value} :=
  (isClopen_payloadCoordinate s value).isOpen.measurableSet.preimage
    (measurable_fst.comp measurable_fst)

private theorem measurableSet_codeNotMemTreeOnWitness (s : List ℕ) :
    MeasurableSet {p : ((Raw × X) × Valuation) | s ∉ p.1.1.tree} :=
  (measurableSet_notMemTree s).preimage (measurable_fst.comp measurable_fst)

private theorem measurableSet_valuationCoordinate (s : List ℕ) (truth : Bool) :
    MeasurableSet {p : ((Raw × X) × Valuation) | p.2 s = truth} := by
  have hmeasurable : Measurable (fun p : ((Raw × X) × Valuation) => p.2 s) :=
    (measurable_pi_apply s).comp measurable_snd
  simpa [Set.preimage, Set.mem_singleton_iff] using
    hmeasurable (measurableSet_singleton truth)

private theorem measurableSet_variableBasicMembership (b : ℕ → Set X)
    (hb : ∀ n, MeasurableSet (b n)) (s : List ℕ) :
    MeasurableSet {p : ((Raw × X) × Valuation) |
      p.1.2 ∈ b (p.1.1.payloadAt s)} := by
  rw [show {p : ((Raw × X) × Valuation) |
      p.1.2 ∈ b (p.1.1.payloadAt s)} =
      ⋃ n : ℕ, {p | p.1.1.payloadAt s = n} ∩ {p | p.1.2 ∈ b n} by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hp
      exact ⟨p.1.1.payloadAt s, rfl, hp⟩
    · rintro ⟨n, hn, hp⟩
      rwa [hn]]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_codePayloadAtOnWitness s n).inter
      ((hb n).preimage (measurable_snd.comp measurable_fst))

private theorem measurableSet_satisfiesAt (b : ℕ → Set X)
    (hb : ∀ n, MeasurableSet (b n)) (s : List ℕ) :
    MeasurableSet {p : ((Raw × X) × Valuation) |
      SatisfiesAt b p.1.1 p.1.2 p.2 s} := by
  have hvTrue := measurableSet_valuationCoordinate (X := X) s true
  have hvFalse := measurableSet_valuationCoordinate (X := X) s false
  have hbasicMem := measurableSet_variableBasicMembership b hb s
  have hbasicEq : MeasurableSet {p : ((Raw × X) × Valuation) |
      p.2 s = true ↔ p.1.2 ∈ b (p.1.1.payloadAt s)} := by
    rw [show {p : ((Raw × X) × Valuation) |
        (p.2 s = true ↔ p.1.2 ∈ b (p.1.1.payloadAt s))} =
        ({p | p.2 s = true} ∩
          {p | p.1.2 ∈ b (p.1.1.payloadAt s)}) ∪
        ({p | p.2 s = false} ∩
          {p | p.1.2 ∈ b (p.1.1.payloadAt s)}ᶜ) by
      ext p
      cases h : p.2 s <;> simp [h]]
    exact (hvTrue.inter hbasicMem).union (hvFalse.inter hbasicMem.compl)
  have hchildTrue := measurableSet_valuationCoordinate (X := X) (s ++ [0]) true
  have hchildFalse := measurableSet_valuationCoordinate (X := X) (s ++ [0]) false
  have hcomplEq : MeasurableSet {p : ((Raw × X) × Valuation) |
      p.2 s = true ↔ p.2 (s ++ [0]) = false} := by
    rw [show {p : ((Raw × X) × Valuation) |
        (p.2 s = true ↔ p.2 (s ++ [0]) = false)} =
        ({p | p.2 s = true} ∩ {p | p.2 (s ++ [0]) = false}) ∪
        ({p | p.2 s = false} ∩ {p | p.2 (s ++ [0]) = true}) by
      ext p
      cases hs : p.2 s <;> cases hc : p.2 (s ++ [0]) <;> simp [hs, hc]]
    exact (hvTrue.inter hchildFalse).union (hvFalse.inter hchildTrue)
  have hexistsTrue : MeasurableSet {p : ((Raw × X) × Valuation) |
      ∃ n, p.2 (s ++ [n]) = true} := by
    rw [show {p : ((Raw × X) × Valuation) | ∃ n, p.2 (s ++ [n]) = true} =
        ⋃ n, {p | p.2 (s ++ [n]) = true} by ext; simp]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_valuationCoordinate (X := X) (s ++ [n]) true
  have hiUnionEq : MeasurableSet {p : ((Raw × X) × Valuation) |
      p.2 s = true ↔ ∃ n, p.2 (s ++ [n]) = true} := by
    rw [show {p : ((Raw × X) × Valuation) |
        (p.2 s = true ↔ ∃ n, p.2 (s ++ [n]) = true)} =
        ({p | p.2 s = true} ∩ {p | ∃ n, p.2 (s ++ [n]) = true}) ∪
        ({p | p.2 s = false} ∩ {p | ∃ n, p.2 (s ++ [n]) = true}ᶜ) by
      ext p
      cases h : p.2 s <;> simp [h]]
    exact (hvTrue.inter hexistsTrue).union (hvFalse.inter hexistsTrue.compl)
  rw [show {p : ((Raw × X) × Valuation) |
      SatisfiesAt b p.1.1 p.1.2 p.2 s} =
      ({p | p.1.1.kindAt? s = some .empty} ∩ {p | p.2 s = false}) ∪
      (({p | p.1.1.kindAt? s = some .basic} ∩
        {p | p.2 s = true ↔ p.1.2 ∈ b (p.1.1.payloadAt s)}) ∪
      (({p | p.1.1.kindAt? s = some .compl} ∩
        {p | p.2 s = true ↔ p.2 (s ++ [0]) = false}) ∪
      ({p | p.1.1.kindAt? s = some .iUnion} ∩
        {p | p.2 s = true ↔ ∃ n, p.2 (s ++ [n]) = true}))) by
    ext p
    cases hkind : p.1.1.kindAt? s with
    | none => simp [SatisfiesAt, hkind]
    | some kind => cases kind <;> simp [SatisfiesAt, hkind]]
  exact ((measurableSet_codeKindAtOnWitness (X := X) s .empty).inter hvFalse).union
    (((measurableSet_codeKindAtOnWitness (X := X) s .basic).inter hbasicEq).union
      (((measurableSet_codeKindAtOnWitness (X := X) s .compl).inter hcomplEq).union
        ((measurableSet_codeKindAtOnWitness (X := X) s .iUnion).inter hiUnionEq)))

/-- Evaluation witnesses form a Borel subset of the code/object/valuation product.
@isnad1 id=measurab.1h3v.s6.783a62906e7b from=translated src=- shape=a7282832 vocab=27418648
-/
theorem measurableSet_evaluationWitnesses (b : ℕ → Set X)
    (hb : ∀ n, MeasurableSet (b n)) (truth : Bool) :
    MeasurableSet (evaluationWitnesses b truth) := by
  rw [show evaluationWitnesses b truth =
      (⋂ s : List ℕ,
        {p : ((Raw × X) × Valuation) | s ∉ p.1.1.tree} ∪
          {p | SatisfiesAt b p.1.1 p.1.2 p.2 s}) ∩
        {p | p.2 [] = truth} by
    ext p
    simp only [evaluationWitnesses, IsEvaluationWitness, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hall, hroot⟩
      exact ⟨fun s => by
        by_cases hs : s ∈ p.1.1.tree
        · exact Or.inr (hall s hs)
        · exact Or.inl hs, hroot⟩
    · rintro ⟨hall, hroot⟩
      refine ⟨?_, hroot⟩
      intro s hs
      rcases hall s with hnot | hsat
      · exact (hnot hs).elim
      · exact hsat]
  exact (MeasurableSet.iInter fun s =>
    (measurableSet_codeNotMemTreeOnWitness (X := X) s).union
      (measurableSet_satisfiesAt b hb s)).inter
    (measurableSet_valuationCoordinate (X := X) [] truth)

/-- Locally invalid code/object pairs are Borel measurable.
@isnad1 id=measurab.0h1v.s6.14c797978a17 from=translated src=- shape=f06fbadd vocab=2043e2a4
-/
theorem measurableSet_locallyInvalidPairs :
    MeasurableSet (locallyInvalidPairs : Set (Raw × X)) := by
  rw [show (locallyInvalidPairs : Set (Raw × X)) =
      (Prod.fst ⁻¹' {c : Raw | IsLocallyValid c})ᶜ by
    ext p
    simp [locallyInvalidPairs]]
  exact (measurableSet_isLocallyValid.preimage measurable_fst).compl

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]

/-- Existence of a prescribed-root evaluation witness is analytic.
@isnad1 id=analytic.1h3v.s6.53aad3a0523b from=translated src=- shape=34fb9d69 vocab=8b4bee51
-/
theorem analyticSet_hasEvaluationWitness (b : ℕ → Set X)
    (hb : ∀ n, MeasurableSet (b n)) (truth : Bool) :
    MeasureTheory.AnalyticSet (hasEvaluationWitness b truth) := by
  rw [show hasEvaluationWitness b truth = Prod.fst '' evaluationWitnesses b truth by rfl]
  exact (measurableSet_evaluationWitnesses b hb truth).analyticSet_image measurable_fst

private theorem analyticSet_union {Y : Type*} [TopologicalSpace Y]
    {s t : Set Y} (hs : MeasureTheory.AnalyticSet s)
    (ht : MeasureTheory.AnalyticSet t) : MeasureTheory.AnalyticSet (s ∪ t) := by
  rw [show s ∪ t = ⋃ value : Bool, if value then s else t by
    ext y
    simp [or_comm]]
  exact MeasureTheory.AnalyticSet.iUnion fun value => by
    cases value <;> simp_all

/--
@isnad1 id=analytic.0h1v.s6.c91147f7c80b from=translated src=- shape=43582020 vocab=be6e0356
-/
theorem analyticSet_locallyInvalidPairs :
    MeasureTheory.AnalyticSet (locallyInvalidPairs : Set (Raw × X)) := by
  have h := measurableSet_locallyInvalidPairs.analyticSet_image
    (f := (id : Raw × X → Raw × X)) measurable_id
  convert h using 1
  ext p
  simp

omit [MeasurableSpace X] [BorelSpace X] in
/-- Ill-founded code/object pairs are analytic by continuous pullback from tree codes.
@isnad1 id=analytic.0h1v.s6.fa5fb4723bc8 from=translated src=- shape=d5892d72 vocab=e7d79511
-/
theorem analyticSet_illFoundedPairs :
    MeasureTheory.AnalyticSet (illFoundedPairs : Set (Raw × X)) := by
  have hcontinuous : Continuous (fun p : Raw × X => p.1.treeCode) :=
    continuous_treeCode.comp continuous_fst
  simpa [illFoundedPairs, Tree.illFoundedTrees, Raw.tree] using
    Tree.analyticSet_illFoundedTrees.preimage hcontinuous

/-- The true-root total evaluation completion is analytic.
@isnad1 id=analytic.1h2v.s6.0a3262164b75 from=translated src=- shape=f0f875c4 vocab=55e45b74
-/
theorem analyticSet_analyticEvaluation (b : ℕ → Set X)
    (hb : ∀ n, MeasurableSet (b n)) :
    MeasureTheory.AnalyticSet (analyticEvaluation b) :=
  analyticSet_union
    (analyticSet_union analyticSet_locallyInvalidPairs analyticSet_illFoundedPairs)
    (analyticSet_hasEvaluationWitness b hb true)

/-- The false-root obstruction is analytic, so its complement is coanalytic.
@isnad1 id=iscoanal.1h2v.s6.8f8345f72e87 from=translated src=- shape=f0f875c4 vocab=d51aeae5
-/
theorem isCoanalytic_coanalyticEvaluation (b : ℕ → Set X)
    (hb : ∀ n, MeasurableSet (b n)) :
    IsCoanalytic (coanalyticEvaluation b) := by
  change MeasureTheory.AnalyticSet
    ((locallyInvalidPairs ∪ illFoundedPairs ∪ hasEvaluationWitness b false)ᶜ)ᶜ
  rw [compl_compl]
  exact analyticSet_union
    (analyticSet_union analyticSet_locallyInvalidPairs analyticSet_illFoundedPairs)
    (analyticSet_hasEvaluationWitness b hb false)

end EvaluationComplexity

/-- The exact locus of valid standard Borel-tree codes.-/
def validCodes : Set Raw :=
  {c | IsValid c}

/-- Add one terminal layer to a tree code. A node is present when it is the new root or its parent
was present in the source tree.-/
def completedTreeCode (T : Tree.TreeCode) : Tree.TreeCode where
  val s := if s = [] then true else T.1 s.dropLast
  property := by
    intro s n hchild
    have hne : s ++ [n] ≠ [] := by
      cases s <;> simp
    have hparent : T.1 s = true := by
      change (if s ++ [n] = [] then true else T.1 (s ++ [n]).dropLast) = true at hchild
      rw [ite_eq_right hne, List.dropLast_concat] at hchild
      exact hchild
    by_cases hs : s = []
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      apply T.2 s.dropLast (s.getLast hs)
      simpa only [List.dropLast_append_getLast hs] using hparent

/--
@isnad1 id=iff.0h2v.s6.6a27a923a0c9 from=translated src=- shape=83ecab2a vocab=d180433a
-/
@[simp]
theorem completedTreeCode_apply_eq_true {T : Tree.TreeCode} {s : List ℕ} :
    (completedTreeCode T).1 s = true ↔ s = [] ∨ T.1 s.dropLast = true := by
  change (if s = [] then true else T.1 s.dropLast) = true ↔ _
  by_cases hs : s = [] <;> simp [hs]

/--
@isnad1 id=iff.0h2v.s8.42d42b4ddcd1 from=translated src=- shape=b0d26fe1 vocab=358b6ef1
-/
theorem mem_completedTreeCode {T : Tree.TreeCode} {s : List ℕ} :
    s ∈ Tree.decodeTree (completedTreeCode T) ↔
      s = [] ∨ s.dropLast ∈ Tree.decodeTree T := by
  simpa only [Tree.mem_decodeTree] using
    (completedTreeCode_apply_eq_true (T := T) (s := s))

/-- Completing a tree by one terminal layer does not change its infinite branches.
@isnad1 id=eq.0h1v.s4.ac79718e2633 from=translated src=- shape=e5fcc717 vocab=c6434ef0
-/
theorem body_completedTreeCode (T : Tree.TreeCode) :
    Tree.body (Tree.decodeTree (completedTreeCode T)) =
      Tree.body (Tree.decodeTree T) := by
  ext x
  constructor
  · intro hx n
    have hnext := hx (n + 1)
    rw [mem_completedTreeCode, Tree.initialSegment_succ,
      List.dropLast_concat] at hnext
    exact hnext.resolve_left (by simp [Tree.initialSegment])
  · intro hx n
    cases n with
    | zero =>
        change (if ([] : List ℕ) = [] then true else T.1 [].dropLast) = true
        simp
    | succ n =>
        rw [mem_completedTreeCode, Tree.initialSegment_succ,
          List.dropLast_concat]
        exact Or.inr (hx n)

/-- Completion preserves and reflects well-foundedness exactly.
@isnad1 id=iff.0h1v.s3.7ffb981a9c56 from=translated src=- shape=4afdac0a vocab=8e46ee4f
-/
theorem isWellFounded_completedTreeCode_iff (T : Tree.TreeCode) :
    Tree.IsWellFounded (Tree.decodeTree (completedTreeCode T)) ↔
      Tree.IsWellFounded (Tree.decodeTree T) := by
  rw [Tree.isWellFounded_iff_body_eq_empty,
    Tree.isWellFounded_iff_body_eq_empty, body_completedTreeCode]

/-- Label the completed source tree by union nodes over source nodes and empty leaves over the
new terminal layer.-/
def validityReduction (T : Tree.TreeCode) : Raw :=
  (completedTreeCode T, fun s =>
    if T.1 s = true then (NodeKind.iUnion.code, 0)
    else (NodeKind.empty.code, 0))

/-- Every output of the reduction satisfies all local validity conditions.
@isnad1 id=islocall.0h1v.s2.12d212a931a6 from=translated src=- shape=76a08d12 vocab=10fb000b
-/
theorem isLocallyValid_validityReduction (T : Tree.TreeCode) :
    IsLocallyValid (validityReduction T) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [validityReduction, Raw.tree, Raw.treeCode, completedTreeCode]
  · intro s hs
    by_cases hT : T.1 s = true <;>
      simp [Raw.IsCoherentAt, IsCoherentLabel, Raw.labels, validityReduction, hT,
        NodeKind.code, NodeKind.ofCode?]
  · intro s hs
    by_cases hT : T.1 s = true
    · simp only [Raw.HasExpectedChildrenAt, Raw.kindAt?, Raw.kindCodeAt,
        Raw.labels, validityReduction, hT, ite_eq_left, NodeKind.code,
        NodeKind.ofCode?]
      intro n
      change s ++ [n] ∈ Tree.decodeTree (completedTreeCode T)
      rw [mem_completedTreeCode, List.dropLast_concat]
      exact Or.inr hT
    · simp only [Raw.HasExpectedChildrenAt, Raw.kindAt?, Raw.kindCodeAt,
        Raw.labels, validityReduction, hT, NodeKind.code,
        NodeKind.ofCode?]
      intro n hchild
      change s ++ [n] ∈ Tree.decodeTree (completedTreeCode T) at hchild
      rw [mem_completedTreeCode, List.dropLast_concat] at hchild
      exact hT (hchild.resolve_left (by simp))

/-- The reduction output is valid exactly when the source tree is well-founded.
@isnad1 id=iff.0h1v.s3.bbf82c7bda54 from=translated src=- shape=8010ab70 vocab=695d7208
-/
theorem isValid_validityReduction_iff (T : Tree.TreeCode) :
    IsValid (validityReduction T) ↔
      Tree.IsWellFounded (Tree.decodeTree T) := by
  rw [isValid_iff_isLocallyValid_and_isWellFounded]
  simp only [isLocallyValid_validityReduction, true_and]
  exact isWellFounded_completedTreeCode_iff T

/-- The one-layer tree completion depends continuously on the source tree code.
@isnad1 id=continuo.0h0v.s6.cf8ea8ec7eee from=translated src=- shape=e3d48bcb vocab=2387333c
-/
theorem continuous_completedTreeCode : Continuous completedTreeCode := by
  apply Continuous.subtype_mk
  exact continuous_pi fun s => by
    by_cases hs : s = []
    · subst s
      simpa [completedTreeCode] using
        (continuous_const : Continuous (fun _ : Tree.TreeCode => true))
    · simpa only [completedTreeCode, hs, ↓reduceIte, Function.comp_def] using
        (continuous_listNatBoolCoordinate s.dropLast).comp continuous_subtype_val

/-- The label component of the validity reduction is continuous.
@isnad1 id=continuo.0h0v.s6.6b701b460429 from=translated src=- shape=662daf4f vocab=5521cdb3
-/
theorem continuous_validityReduction_labels :
    Continuous (fun T : Tree.TreeCode => (validityReduction T).labels) := by
  exact continuous_pi fun s => by
    have hcoordinate : Continuous (fun T : Tree.TreeCode => T.1 s) :=
      (continuous_listNatBoolCoordinate s).comp continuous_subtype_val
    have hlabel : Continuous (fun value : Bool =>
        if value = true then (NodeKind.iUnion.code, 0)
        else (NodeKind.empty.code, 0)) :=
      continuous_of_discreteTopology
    change Continuous (fun T : Tree.TreeCode =>
      if T.1 s = true then (NodeKind.iUnion.code, 0)
      else (NodeKind.empty.code, 0))
    simpa only [Function.comp_def] using hlabel.comp hcoordinate

/-- The exact well-foundedness-to-validity reduction map is continuous.
@isnad1 id=continuo.0h0v.s6.2e0efdf86985 from=translated src=- shape=54c8eceb vocab=bc9fa54e
-/
theorem continuous_validityReduction : Continuous validityReduction := by
  change Continuous (fun T : Tree.TreeCode =>
    (completedTreeCode T, fun s =>
      if T.1 s = true then (NodeKind.iUnion.code, 0)
      else (NodeKind.empty.code, 0)))
  exact continuous_completedTreeCode.prodMk continuous_validityReduction_labels

private def locallyInvalidCodes : Set Raw :=
  {c | ¬IsLocallyValid c}

private def illFoundedCodes : Set Raw :=
  {c | ¬Tree.IsWellFounded c.tree}

private theorem analyticSet_locallyInvalidCodes :
    MeasureTheory.AnalyticSet locallyInvalidCodes := by
  have hm : MeasurableSet locallyInvalidCodes := by
    rw [show locallyInvalidCodes = {c : Raw | IsLocallyValid c}ᶜ by
      ext c
      simp [locallyInvalidCodes]]
    exact measurableSet_isLocallyValid.compl
  have h := hm.analyticSet_image (f := (id : Raw → Raw)) measurable_id
  convert h using 1
  ext c
  simp

private theorem analyticSet_illFoundedCodes :
    MeasureTheory.AnalyticSet illFoundedCodes := by
  simpa [illFoundedCodes, Tree.illFoundedTrees, Raw.tree] using
    Tree.analyticSet_illFoundedTrees.preimage continuous_treeCode

/-- The exact valid-code locus is coanalytic.
@isnad1 id=iscoanal.0h0v.s6.04995cf594d1 from=translated src=- shape=25b03439 vocab=cdfc3337
-/
theorem isCoanalytic_validCodes : IsCoanalytic validCodes := by
  change MeasureTheory.AnalyticSet validCodesᶜ
  rw [show validCodesᶜ = locallyInvalidCodes ∪ illFoundedCodes by
    ext c
    simp only [validCodes, locallyInvalidCodes, illFoundedCodes,
      Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
    rw [isValid_iff_isLocallyValid_and_isWellFounded]
    constructor
    · intro h
      by_cases hlocal : IsLocallyValid c
      · exact Or.inr (fun hwf => h ⟨hlocal, hwf⟩)
      · exact Or.inl hlocal
    · rintro (hlocal | hwf) hvalid
      · exact hlocal hvalid.1
      · exact hwf hvalid.2]
  exact analyticSet_union analyticSet_locallyInvalidCodes analyticSet_illFoundedCodes

/-- The explicit completion map continuously reduces well-founded tree codes to valid Borel-tree
codes, preserving and reflecting membership.
@isnad1 id=continuo.0h0v.s6.2d098f062e0f from=translated src=- shape=93eefbde vocab=9c1917f8
-/
theorem continuouslyReduces_wellFoundedTrees_validCodes :
    ContinuouslyReduces Tree.wellFoundedTrees validCodes :=
  continuouslyReduces_of_continuous validityReduction continuous_validityReduction fun T => by
    simpa [Tree.wellFoundedTrees, validCodes] using (isValid_validityReduction_iff T).symm

/-- The valid-code set is coanalytic-complete for Baire-space sources, with the exact reduction
factored through the standard well-founded-tree complete set.
@isnad1 id=iscoanal.0h0v.s6.bae74729caeb from=translated src=- shape=25b03439 vocab=65bf89e6
-/
theorem validCodes_complete : IsCoanalyticCompleteForBaire validCodes := by
  refine ⟨isCoanalytic_validCodes, ?_⟩
  intro s hs
  exact (Tree.continuouslyReduces_wellFoundedTrees_of_isCoanalytic hs).trans
    continuouslyReduces_wellFoundedTrees_validCodes

end DescriptiveSetTheory.BorelTreeCode
