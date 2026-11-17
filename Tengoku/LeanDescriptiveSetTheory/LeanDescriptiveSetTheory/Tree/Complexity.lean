/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.Coanalytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.CodeSpace
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.WellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complexity of ill-founded and well-founded tree codes

The relation between a coded tree and one of its Baire-space branches is closed. Projecting that
relation onto the tree coordinate shows that the ill-founded codes form an analytic set. The
well-founded codes are its exact complement and are therefore coanalytic.

This file proves pointclass membership and complement laws only. Completeness under continuous
reducibility belongs to the next release.
-/

open Set

namespace DescriptiveSetTheory.Tree

/-- Pairs consisting of a coded tree and an infinite branch through its decoded tree.-/
def treeBranchRelation : Set (TreeCode × (ℕ → ℕ)) :=
  {p | p.2 ∈ body (decodeTree p.1)}

@[simp]
theorem mem_treeBranchRelation {c : TreeCode} {x : ℕ → ℕ} :
    (c, x) ∈ treeBranchRelation ↔ x ∈ body (decodeTree c) :=
  Iff.rfl

private theorem isOpen_treeBranchConstraintValue (n : ℕ) (b : Bool) :
    IsOpen {p : TreeCode × (ℕ → ℕ) |
      p.1.1 (initialSegment p.2 n) = b} := by
  rw [show {p : TreeCode × (ℕ → ℕ) |
      p.1.1 (initialSegment p.2 n) = b} =
      ⋃ s : Fin n → ℕ,
        {c : TreeCode | c.1 (List.ofFn s) = b} ×ˢ
          {x : ℕ → ℕ | (fun i : Fin n => x i) = s} by
    ext p
    constructor
    · intro hp
      refine Set.mem_iUnion.2 ⟨(fun i : Fin n => p.2 i), ?_⟩
      exact ⟨by simpa [initialSegment] using hp, rfl⟩
    · intro hp
      rcases Set.mem_iUnion.1 hp with ⟨s, hs, hprefix⟩
      change p.1.1 (List.ofFn fun i : Fin n => p.2 i) = b
      rw [hprefix]
      exact hs]
  exact isOpen_iUnion fun s => by
    have hcode : Continuous (fun c : TreeCode => c.1 (List.ofFn s)) :=
      (continuous_listNatBoolCoordinate (List.ofFn s)).comp continuous_subtype_val
    have hopenCode : IsOpen {c : TreeCode | c.1 (List.ofFn s) = b} := by
      simpa [Set.preimage, Set.mem_singleton_iff] using (isOpen_discrete {b}).preimage hcode
    have hprefix : Continuous (fun x : ℕ → ℕ => fun i : Fin n => x i) :=
      continuous_pi fun i => continuous_apply (i : ℕ)
    have hopenPrefix : IsOpen {x : ℕ → ℕ | (fun i : Fin n => x i) = s} := by
      simpa [Set.preimage, Set.mem_singleton_iff] using (isOpen_discrete {s}).preimage hprefix
    exact hopenCode.prod hopenPrefix

private theorem isClosed_treeBranchConstraint (n : ℕ) :
    IsClosed {p : TreeCode × (ℕ → ℕ) |
      p.1.1 (initialSegment p.2 n) = true} := by
  rw [← isOpen_compl_iff]
  have hcompl :
      {p : TreeCode × (ℕ → ℕ) |
        p.1.1 (initialSegment p.2 n) = true}ᶜ =
      {p : TreeCode × (ℕ → ℕ) |
        p.1.1 (initialSegment p.2 n) = false} := by
    ext p
    cases h : p.1.1 (initialSegment p.2 n) <;> simp [h]
  rw [hcompl]
  exact isOpen_treeBranchConstraintValue n false

/-- The relation between a valid tree code and an infinite branch is closed.-/
theorem isClosed_treeBranchRelation : IsClosed treeBranchRelation := by
  rw [show treeBranchRelation = ⋂ n,
      {p : TreeCode × (ℕ → ℕ) |
        p.1.1 (initialSegment p.2 n) = true} by
    ext p
    simp [treeBranchRelation, body, IsBranch]]
  exact isClosed_iInter isClosed_treeBranchConstraint

/-- The set of valid tree codes whose decoded trees have an infinite branch.-/
def illFoundedTrees : Set TreeCode :=
  {c | ¬ IsWellFounded (decodeTree c)}

/-- The set of valid tree codes whose decoded trees have no infinite branch.-/
def wellFoundedTrees : Set TreeCode :=
  {c | IsWellFounded (decodeTree c)}

@[simp]
theorem mem_illFoundedTrees {c : TreeCode} :
    c ∈ illFoundedTrees ↔ ¬ IsWellFounded (decodeTree c) :=
  Iff.rfl

@[simp]
theorem mem_wellFoundedTrees {c : TreeCode} :
    c ∈ wellFoundedTrees ↔ IsWellFounded (decodeTree c) :=
  Iff.rfl

/-- Ill-founded codes are exactly the first-coordinate projection of the closed branch relation.-/
theorem illFoundedTrees_eq_fst_image_treeBranchRelation :
    illFoundedTrees = Prod.fst '' treeBranchRelation := by
  ext c
  constructor
  · intro hc
    rw [mem_illFoundedTrees, isWellFounded_iff_body_eq_empty] at hc
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hc
    exact ⟨(c, x), hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    rw [mem_illFoundedTrees, isWellFounded_iff_body_eq_empty]
    exact Set.nonempty_iff_ne_empty.mp ⟨p.2, hp⟩

/-- The set of ill-founded tree codes is analytic.-/
theorem analyticSet_illFoundedTrees :
    MeasureTheory.AnalyticSet illFoundedTrees := by
  rw [illFoundedTrees_eq_fst_image_treeBranchRelation]
  exact isClosed_treeBranchRelation.analyticSet.image_of_continuous continuous_fst

/-- Well-founded and ill-founded tree codes are exact complements.-/
theorem wellFoundedTrees_eq_compl : wellFoundedTrees = illFoundedTreesᶜ := by
  ext c
  simp [wellFoundedTrees, illFoundedTrees]

/-- The set of well-founded tree codes is coanalytic.-/
theorem isCoanalytic_wellFoundedTrees : IsCoanalytic wellFoundedTrees := by
  simpa [IsCoanalytic, wellFoundedTrees_eq_compl] using analyticSet_illFoundedTrees

/-- No valid tree code is both ill-founded and well-founded.-/
theorem disjoint_illFoundedTrees_wellFoundedTrees :
    Disjoint illFoundedTrees wellFoundedTrees := by
  rw [wellFoundedTrees_eq_compl]
  exact disjoint_compl_right

/-- Every valid tree code is either ill-founded or well-founded.-/
theorem illFoundedTrees_union_wellFoundedTrees :
    illFoundedTrees ∪ wellFoundedTrees = Set.univ := by
  rw [wellFoundedTrees_eq_compl, union_compl_self]

end DescriptiveSetTheory.Tree
