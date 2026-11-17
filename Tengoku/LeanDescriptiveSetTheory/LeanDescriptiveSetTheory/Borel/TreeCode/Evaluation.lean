/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.Coanalytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.TreeCode.Decode
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Complexity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Total evaluation relations for coded Borel trees -/

open Set

universe u

namespace DescriptiveSetTheory.BorelTreeCode

variable {X : Type u}

/-- Validity without the well-foundedness clause. This is the local, Borel part of validity.-/
structure IsLocallyValid (c : Raw) : Prop where
  root_mem : [] ∈ c.tree
  coherent : ∀ s, s ∈ c.tree → c.IsCoherentAt s
  expectedChildren : ∀ s, s ∈ c.tree → c.HasExpectedChildrenAt s

/-- Exact decomposition of validity into local coherence and well-foundedness.
@isnad1 id=iff.0h1v.s3.ed1fc812b0d5 from=translated src=- shape=9038ff84 vocab=212b3294
-/
theorem isValid_iff_isLocallyValid_and_isWellFounded {c : Raw} :
    IsValid c ↔ IsLocallyValid c ∧ Tree.IsWellFounded c.tree := by
  constructor
  · intro h
    exact ⟨⟨h.root_mem, h.coherent, h.expectedChildren⟩, h.wellFounded⟩
  · rintro ⟨hlocal, hwf⟩
    exact ⟨hlocal.root_mem, hwf, hlocal.coherent, hlocal.expectedChildren⟩

/-- Every valid code is locally valid.
@isnad1 id=islocall.1h1v.s2.a30e75d0bc10 from=translated src=- shape=6321fd23 vocab=ac6c7fa1
-/
theorem IsValid.isLocallyValid {c : Raw} (h : IsValid c) : IsLocallyValid c :=
  isValid_iff_isLocallyValid_and_isWellFounded.mp h |>.1

/-- A Boolean truth assignment on all finite syntax-tree coordinates.-/
abbrev Valuation := List ℕ → Bool

/-- The local semantic equation at one node. Coordinates outside the raw tree are irrelevant.-/
def SatisfiesAt (b : ℕ → Set X) (c : Raw) (x : X) (v : Valuation)
    (s : List ℕ) : Prop :=
  match c.kindAt? s with
  | some .empty => v s = false
  | some .basic => v s = true ↔ x ∈ b (c.payloadAt s)
  | some .compl => v s = true ↔ v (s ++ [0]) = false
  | some .iUnion => v s = true ↔ ∃ n, v (s ++ [n]) = true
  | none => False

/-- A valuation satisfies every local semantic equation on the raw tree.-/
def IsEvaluationWitness (b : ℕ → Set X) (c : Raw) (x : X)
    (v : Valuation) : Prop :=
  ∀ s, s ∈ c.tree → SatisfiesAt b c x v s

/-- The canonical valuation induced by the proof-gated v2.3 semantics.-/
noncomputable def canonicalValuation (b : ℕ → Set X) (c : Raw) (h : IsValid c)
    (x : X) (s : List ℕ) : Bool := by
  classical
  exact if hs : s ∈ c.tree then
    if x ∈ evalAt b c h ⟨s, hs⟩ then true else false
  else false

/--
@isnad1 id=iff.2h5v.s8.aa7e4c8e37af from=translated src=- shape=fc31ddd6 vocab=f686830c
-/
@[simp]
theorem canonicalValuation_eq_true_iff (b : ℕ → Set X) {c : Raw} (h : IsValid c)
    (x : X) {s : List ℕ} (hs : s ∈ c.tree) :
    canonicalValuation b c h x s = true ↔ x ∈ evalAt b c h ⟨s, hs⟩ := by
  classical
  simp [canonicalValuation, hs]

/--
@isnad1 id=iff.2h5v.s8.9226b4e7a9de from=translated src=- shape=05977373 vocab=44cde010
-/
@[simp]
theorem canonicalValuation_eq_false_iff (b : ℕ → Set X) {c : Raw} (h : IsValid c)
    (x : X) {s : List ℕ} (hs : s ∈ c.tree) :
    canonicalValuation b c h x s = false ↔ x ∉ evalAt b c h ⟨s, hs⟩ := by
  classical
  simp [canonicalValuation, hs]

/-- Witnesses with a prescribed root truth value.-/
def evaluationWitnesses (b : ℕ → Set X) (truth : Bool) :
    Set ((Raw × X) × Valuation) :=
  {p | IsEvaluationWitness b p.1.1 p.1.2 p.2 ∧ p.2 [] = truth}

/-- Existence of a local evaluation witness with prescribed root truth.-/
def hasEvaluationWitness (b : ℕ → Set X) (truth : Bool) : Set (Raw × X) :=
  Prod.fst '' evaluationWitnesses b truth

/-- Raw pairs whose code fails local validity.-/
def locallyInvalidPairs : Set (Raw × X) :=
  {p | ¬ IsLocallyValid p.1}

/-- Raw pairs whose underlying syntax tree is ill-founded.-/
def illFoundedPairs : Set (Raw × X) :=
  {p | ¬ Tree.IsWellFounded p.1.tree}

/-- Total analytic completion. Every invalid code is true; a valid code is governed by a
true-root local evaluation witness.-/
def analyticEvaluation (b : ℕ → Set X) : Set (Raw × X) :=
  locallyInvalidPairs ∪ illFoundedPairs ∪ hasEvaluationWitness b true

/-- Total coanalytic completion. Every invalid code is false; a valid code is true exactly when
there is no false-root local evaluation witness.-/
def coanalyticEvaluation (b : ℕ → Set X) : Set (Raw × X) :=
  (locallyInvalidPairs ∪ illFoundedPairs ∪ hasEvaluationWitness b false)ᶜ

/-- A valid code belongs to neither invalid-code completion branch.
@isnad1 id=not.1h3v.s5.4c31dbfa3298 from=translated src=- shape=ec40c0b8 vocab=d1a25794
-/
theorem valid_not_mem_invalidPairs {c : Raw} (h : IsValid c) (x : X) :
    (c, x) ∉ locallyInvalidPairs ∪ illFoundedPairs := by
  rintro (hlocal | hill)
  · exact hlocal h.isLocallyValid
  · exact hill h.wellFounded

/-- Invalid codes have opposite completed truth values, independently of the object.
@isnad1 id=and.1h4v.s5.3504ab60e636 from=translated src=- shape=84237f9d vocab=d0203955
-/
theorem evaluation_disagrees_of_not_isValid (b : ℕ → Set X) {c : Raw}
    (h : ¬ IsValid c) (x : X) :
    (c, x) ∈ analyticEvaluation b ∧ (c, x) ∉ coanalyticEvaluation b := by
  have hinvalid : ¬IsLocallyValid c ∨ ¬Tree.IsWellFounded c.tree := by
    by_contra hboth
    push Not at hboth
    exact h (isValid_iff_isLocallyValid_and_isWellFounded.mpr hboth)
  rcases hinvalid with hlocal | hill
  · exact ⟨Or.inl (Or.inl hlocal), fun hco => hco (Or.inl (Or.inl hlocal))⟩
  · exact ⟨Or.inl (Or.inr hill), fun hco => hco (Or.inl (Or.inr hill))⟩

end DescriptiveSetTheory.BorelTreeCode
