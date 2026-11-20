/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.PairDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directed pair uniformity and nonuniformity witnesses

Pair regularity in this library is **directed** and phrased on **ordered blocks**:
`IsUniformPair R X Y ε` says every pair of `ε`-large sub-blocks `X' ⊆ X`, `Y' ⊆ Y` has
pair density within `ε` of the whole block's. Thresholds and deviations are real, with
`0 < ε` assumed where substantive; regularity uses `≤ ε`, so failing it yields a
**strict** witness: a `NonuniformWitness` records the deviating sub-rectangle as data
(the refinement step needs the subsets definitionally, not just existentially).

The predicate/negation/witness architecture follows mathlib's
`SimpleGraph.IsUniform` / `not_isUniform_iff` and its chosen-witness API
(`Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform`), adapted to an arbitrary
directed relation. **Deliberate divergence from mathlib:** mathlib defines uniformity
with strict deviation `< ε` (failure gives `ε ≤` witnesses); this library uses `≤ ε`
so that failure gives strict `ε <` witnesses — a repository API decision. Directed
regularity in the literature: N. Alon and A. Shapira, *Testing Subgraphs in Directed
Graphs*, JCSS 69 (2004), §3 (their multi-density digraph setting is stronger than the
single arbitrary relation treated here).
-/

namespace RegularityLemmata

variable {α : Type*} {R : α → α → Prop} [DecidableRel R] {X Y A B : Finset α} {ε : ℝ}

/-- **Directed cut-uniformity**: all `ε`-large ordered sub-blocks have density within
`ε` of the whole pair's.-/
def IsUniformPair (R : α → α → Prop) [DecidableRel R] (X Y : Finset α) (ε : ℝ) : Prop :=
  ∀ ⦃X' : Finset α⦄, X' ⊆ X → ∀ ⦃Y' : Finset α⦄, Y' ⊆ Y →
    ε * (X.card : ℝ) ≤ (X'.card : ℝ) → ε * (Y.card : ℝ) ≤ (Y'.card : ℝ) →
    |pairDensity R X' Y' - pairDensity R X Y| ≤ ε

/-- Uniformity weakens as `ε` grows, unconditionally.
@isnad1 id=isunifor.2h6v.s5.990ef5095ac5 from=translated src=- shape=895f5302 vocab=11577d3e
-/
theorem IsUniformPair.mono {ε' : ℝ} (hεε : ε ≤ ε') (h : IsUniformPair R X Y ε) :
    IsUniformPair R X Y ε' := by
  intro X' hX' Y' hY' hXc hYc
  have hε0 : (0 : ℝ) ≤ ε' - ε := by linarith
  refine le_trans (h hX' hY' ?_ ?_) hεε
  · calc ε * (X.card : ℝ) ≤ ε' * (X.card : ℝ) :=
        mul_le_mul_of_nonneg_right hεε (Nat.cast_nonneg _)
      _ ≤ (X'.card : ℝ) := hXc
  · calc ε * (Y.card : ℝ) ≤ ε' * (Y.card : ℝ) :=
        mul_le_mul_of_nonneg_right hεε (Nat.cast_nonneg _)
      _ ≤ (Y'.card : ℝ) := hYc

/-- Everything is `1`-uniform: densities live in `[0, 1]`.
@isnad1 id=isunifor.0h4v.s4.e5848f6635f5 from=translated src=- shape=c435821f vocab=fab0099a
-/
theorem isUniformPair_one : IsUniformPair R X Y 1 := by
  intro X' _ Y' _ _ _
  have h1 := pairDensity_le_one (R := R) (A := X') (B := Y')
  have h2 := pairDensity_nonneg (R := R) (A := X') (B := Y')
  have h3 := pairDensity_le_one (R := R) (A := X) (B := Y)
  have h4 := pairDensity_nonneg (R := R) (A := X) (B := Y)
  rw [abs_le]
  constructor <;> linarith

/-- Constructive witness that `(A, B)` fails `ε`-uniformity: an explicit pair of
`ε`-large sub-blocks whose density deviates from the parent's by **strictly** more
than `ε`.-/
structure NonuniformWitness (R : α → α → Prop) [DecidableRel R] (A B : Finset α)
    (ε : ℝ) where
  /-- The sub-rectangle's left side, `⊆ A`.-/
  left : Finset α
  /-- The sub-rectangle's right side, `⊆ B`.-/
  right : Finset α
  left_subset : left ⊆ A
  right_subset : right ⊆ B
  /-- `left` is `ε`-large in `A`.-/
  left_card : ε * (A.card : ℝ) ≤ (left.card : ℝ)
  /-- `right` is `ε`-large in `B`.-/
  right_card : ε * (B.card : ℝ) ≤ (right.card : ℝ)
  /-- The density deviation strictly exceeds `ε`.-/
  dev : ε < |pairDensity R left right - pairDensity R A B|

/-- The `∃`-form of nonuniformity (the `Prop` dual of `NonuniformWitness`).-/
def IsNonuniformPair (R : α → α → Prop) [DecidableRel R] (A B : Finset α) (ε : ℝ) :
    Prop :=
  ∃ A' ⊆ A, ∃ B' ⊆ B,
    ε * (A.card : ℝ) ≤ (A'.card : ℝ) ∧ ε * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
    ε < |pairDensity R A' B' - pairDensity R A B|

/-- Failing `ε`-uniformity is exactly being `ε`-nonuniform.
@isnad1 id=iff.0h5v.s5.bb09f6513329 from=translated src=- shape=09882c11 vocab=5486fe3f
-/
theorem not_isUniformPair_iff :
    ¬ IsUniformPair R A B ε ↔ IsNonuniformPair R A B ε := by
  unfold IsUniformPair IsNonuniformPair
  push Not
  rfl

/-- Extract a constructive witness from a failure of `ε`-uniformity.-/
noncomputable def NonuniformWitness.ofNotUniform (h : ¬ IsUniformPair R A B ε) :
    NonuniformWitness R A B ε := by
  rw [not_isUniformPair_iff] at h
  choose A' hA' B' hB' hAc hBc hdev using h
  exact ⟨A', B', hA', hB', hAc, hBc, hdev⟩

/--
@isnad1 id=isnonuni.0h6v.s5.1fcfce2113fd from=translated src=- shape=3cd9f037 vocab=bf206efc
-/
theorem IsNonuniformPair.of_witness (w : NonuniformWitness R A B ε) :
    IsNonuniformPair R A B ε :=
  ⟨w.left, w.left_subset, w.right, w.right_subset, w.left_card, w.right_card, w.dev⟩

/--
@isnad1 id=not.0h6v.s5.070392a1ebf5 from=translated src=- shape=40f187fd vocab=dc00b016
-/
theorem not_isUniformPair_of_witness (w : NonuniformWitness R A B ε) :
    ¬ IsUniformPair R A B ε :=
  not_isUniformPair_iff.mpr (IsNonuniformPair.of_witness w)

/-! ### Tests and adversarial examples -/

-- Everything is 1-uniform, instantiated.

end RegularityLemmata
