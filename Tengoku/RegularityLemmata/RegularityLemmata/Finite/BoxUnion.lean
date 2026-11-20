/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.ProductBox
import Tengoku.Seed.Data.Finset.SymmDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite unions of boxes and the weighted symmetric-difference error

A finite family of boxes covers the tuples lying in at least one of them. Two such families are
compared by the **weighted mass of the tuples covered by exactly one** — their symmetric
difference. That number is the error a consumer charges for replacing one family by the other.

## Semantic unions, no Boolean syntax

A union here is a `Finset (FiniteBox V)` together with the tuple set it covers. There is
deliberately **no** syntax tree of Boolean combinations: finsets of tuples, finite unions, and
explicit mass bounds are enough, and a syntax would have to be designed against a consumer that
does not yet exist.

## One notion of mass, again

There is no mass primitive here. A symmetric difference is not a box, so the error cannot be
written with `boxMass` — but it is still a weighted sum over a finite set of tuples, which is
exactly `finsetMass` applied to `tupleWeight w`. That is what is used throughout, with
`boxMass_eq_finsetMass_tupleWeight` recording that `boxMass` is the same thing on a box's tuples.

The generic estimates it rests on — subadditivity, the union bound over a family, and the
symmetric-difference bound on a mass difference — are properties of `finsetMass` and live in
`RegularityLemmata/Finite/Weight.lean` alongside it, not here.

## Why this is a separate module

`Finset.biUnion` and symmetric difference on tuple sets both need `DecidableEq (∀ i, V i)`, which
in turn needs `[∀ i, DecidableEq (V i)]` fiberwise. `RegularityLemmata/Finite/ProductBox.lean`
deliberately carries no decidable equality on the carriers, so — exactly as with
`RegularityLemmata/Partition/BoxPartition.lean` — the heavier instances are confined here and
`FiniteBox`, `boxMass`, `boxPredMass`, and `boxDensity` keep their lighter profile.

## Where nonnegativity enters, and where it does not

Everything that is an **identity** is hypothesis-free and survives signed weights: additivity
over a disjoint family, symmetry of the error, and its vanishing against itself.

Nonnegativity is required exactly for the **metric-style** claims — the union bound, the triangle
inequality, and the bound of a mass difference by the error — because each compares masses of
different sets, and with signed weights a larger set can carry less mass. The hypotheses are
stated on the sets involved, never globally.

The mass-difference bound needs nonnegativity only on the **symmetric difference**: the shared
intersection cancels between the two masses, so the weight there is unconstrained.
-/

namespace RegularityLemmata

open scoped symmDiff

variable {ι : Type*} {V : ι → Type*}

/-! ### Unions of a finite family of boxes -/

/-- **The tuples covered by a finite family of boxes.**-/
def unionTuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (F : Finset (FiniteBox V)) : Finset (∀ i, V i) :=
  F.biUnion FiniteBox.tuples

/--
@isnad1 id=iff.0h4v.s7.bbe5a6514652 from=translated src=- shape=d4b61f2c vocab=358f7783
-/
@[simp] theorem mem_unionTuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {F : Finset (FiniteBox V)} {x : ∀ i, V i} :
    x ∈ unionTuples F ↔ ∃ A ∈ F, x ∈ A.tuples := Finset.mem_biUnion

/--
@isnad1 id=eq.0h2v.s5.2e726b0f1078 from=translated src=- shape=6befe62d vocab=24ecf444
-/
@[simp] theorem unionTuples_empty [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] :
    unionTuples (∅ : Finset (FiniteBox V)) = ∅ := Finset.biUnion_empty

/--
@isnad1 id=eq.0h3v.s5.0d9adbcd4355 from=translated src=- shape=6c72f857 vocab=4d06c9db
-/
@[simp] theorem unionTuples_singleton [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (A : FiniteBox V) : unionTuples {A} = A.tuples := Finset.singleton_biUnion

/--
@isnad1 id=le.1h4v.s6.bc90ddba2d0a from=translated src=- shape=5f5a55cb vocab=f4821ca7
-/
theorem unionTuples_subset [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {F G : Finset (FiniteBox V)} (h : F ⊆ G) : unionTuples F ⊆ unionTuples G :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- **`boxMass` is `finsetMass` of the tuple weight**, over the box's tuples. Stated so that the
box layer and the generic weight layer never drift apart, and so the results below can be phrased
with one mass notion.
@isnad1 id=eq.0h4v.s5.362bc3f19dd1 from=translated src=- shape=2dbcac0e vocab=e140f964
-/
theorem boxMass_eq_finsetMass_tupleWeight [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxMass w A = finsetMass (tupleWeight w) A.tuples := rfl

/-- **Exact additivity for a disjoint family.** An identity: no positivity hypothesis, so signed
weights are fine.
@isnad1 id=eq.1h4v.s6.0671b0489a8d from=translated src=- shape=0d094e66 vocab=81976ef3
-/
theorem finsetMass_unionTuples_of_pairwiseDisjoint [Fintype ι] [DecidableEq ι]
    [∀ i, DecidableEq (V i)] (w : ∀ i, V i → ℝ) {F : Finset (FiniteBox V)}
    (h : (F : Set (FiniteBox V)).PairwiseDisjoint FiniteBox.tuples) :
    finsetMass (tupleWeight w) (unionTuples F) = ∑ A ∈ F, boxMass w A :=
  Finset.sum_biUnion h

/-- **The union bound**, which does need nonnegativity. A direct specialization of the generic
`finsetMass_biUnion_le`.
@isnad1 id=le.1h4v.s7.665283ced807 from=translated src=- shape=21e7d35e vocab=2418e619
-/
theorem finsetMass_unionTuples_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F, 0 ≤ tupleWeight w x) :
    finsetMass (tupleWeight w) (unionTuples F) ≤ ∑ A ∈ F, boxMass w A :=
  finsetMass_biUnion_le hw

/-! ### The weighted symmetric-difference error -/

/-- **The error between two finite unions of boxes**: the weighted mass of the tuples covered by
exactly one of them.-/
def boxUnionError [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] (w : ∀ i, V i → ℝ)
    (F G : Finset (FiniteBox V)) : ℝ :=
  finsetMass (tupleWeight w) (unionTuples F ∆ unionTuples G)

/--
@isnad1 id=eq.0h5v.s7.01931fa180ce from=translated src=- shape=9f63a649 vocab=8370d484
-/
theorem boxUnionError_apply [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F G : Finset (FiniteBox V)) :
    boxUnionError w F G = finsetMass (tupleWeight w) (unionTuples F ∆ unionTuples G) := rfl

/-- **Symmetric, with no hypothesis.**
@isnad1 id=eq.0h5v.s5.1a5e2130ee6b from=translated src=- shape=29fb0ed4 vocab=e2e05539
-/
theorem boxUnionError_comm [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F G : Finset (FiniteBox V)) :
    boxUnionError w F G = boxUnionError w G F := by
  rw [boxUnionError, boxUnionError, symmDiff_comm]

/-- **Zero against itself, with no hypothesis** — an identity, not an estimate, so signed
weights are fine.
@isnad1 id=eq.0h4v.s5.f688ce68c809 from=translated src=- shape=86da647e vocab=e2e05539
-/
@[simp] theorem boxUnionError_self [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F : Finset (FiniteBox V)) : boxUnionError w F F = 0 := by
  rw [boxUnionError, symmDiff_self]
  exact finsetMass_empty _

/-- Families covering the same tuples have zero error.

Stated in one direction only, and that is the correct contract: the converse is **false**, since
a nonempty symmetric difference of zero-weight tuples also has zero error.
@isnad1 id=eq.1h5v.s6.77c6a4d73c23 from=translated src=- shape=852b2c95 vocab=d1cb1a7b
-/
theorem boxUnionError_of_unionTuples_eq [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {F G : Finset (FiniteBox V)} (h : unionTuples F = unionTuples G) :
    boxUnionError w F G = 0 := by
  rw [boxUnionError, h, symmDiff_self]
  exact finsetMass_empty _

/--
@isnad1 id=le.1h5v.s7.7eb9e8e31df3 from=translated src=- shape=c703f7b4 vocab=7093dc89
-/
theorem boxUnionError_nonneg [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F ∆ unionTuples G, 0 ≤ tupleWeight w x) :
    0 ≤ boxUnionError w F G := finsetMass_nonneg hw

/-- **The triangle inequality.** Nonnegativity is needed on the union of the two pairwise
differences, which is where the intermediate family's own tuples enter.
@isnad1 id=le.1h6v.s8.c094a1a76fa6 from=translated src=- shape=38c873b5 vocab=f9e9c29e
-/
theorem boxUnionError_triangle [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G H : Finset (FiniteBox V)}
    (hw : ∀ x ∈ (unionTuples F ∆ unionTuples G) ∪ (unionTuples G ∆ unionTuples H),
      0 ≤ tupleWeight w x) :
    boxUnionError w F H ≤ boxUnionError w F G + boxUnionError w G H :=
  le_trans (finsetMass_mono hw (symmDiff_triangle _ _ _)) (finsetMass_union_le hw)

/-- **A mass difference between two unions is controlled by the error.** One-sided, assuming
neither disjointness nor nesting, and needing nonnegativity only on the symmetric difference.
@isnad1 id=le.1h5v.s7.145f68ff1ff2 from=translated src=- shape=fff82a05 vocab=22e5ce23
-/
theorem abs_sub_finsetMass_unionTuples_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F ∆ unionTuples G, 0 ≤ tupleWeight w x) :
    |finsetMass (tupleWeight w) (unionTuples F)
        - finsetMass (tupleWeight w) (unionTuples G)| ≤ boxUnionError w F G :=
  abs_sub_finsetMass_le hw

/-! ### Tests -/

section Tests

private abbrev VU : Fin 2 → Type := fun _ => Fin 2

private instance : ∀ i, DecidableEq (VU i) := fun _ => inferInstanceAs (DecidableEq (Fin 2))

/-- The box fixing the first coordinate to `v` and leaving the second free.-/
private def slab (v : Fin 2) : FiniteBox VU := fun i => if i = 0 then {v} else Finset.univ

private def fullBox : FiniteBox VU := fun _ => Finset.univ

/-- A weight that is negative on part of the carrier, used to show the identities survive it.-/
private def wU : ∀ i, VU i → ℝ := fun _ v => if v = 0 then 2 else -1

end Tests

end RegularityLemmata
