/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.ProductBox
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Basic
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independent coordinate partitions of a weighted box

Partitioning each coordinate of a box independently partitions the box: a **product cell** is a
choice of one part in every coordinate, and the tuples of a box are exactly the tuples of its
product cells, each counted once.

## Why this is a separate module

`RegularityLemmata/Finite/ProductBox.lean` is deliberately instance-light: it needs `[Fintype ι]`
and `[DecidableEq ι]`, and **no** decidable equality on the carriers. `Finpartition (A i)` needs the
lattice structure on `Finset (V i)`, hence `[DecidableEq (V i)]` fiberwise. That requirement is
legitimate here — the cells are manipulated as finite families of finsets — but it must not leak
backwards, so it is confined to this module and `FiniteBox`, `boxMass`, and `boxDensity` keep
their lighter instance profile.

The instances are written out at every declaration rather than hidden behind `classical`, so a
reader can see exactly what each result costs.

## Refinement direction

`RegularityLemmata/Partition/Basic.lean` fixes the convention: in the `Finpartition` order, `Q ≤ P`
means `Q` is
**finer** than `P`. Refinement of a box partition is that relation coordinatewise,
`∀ i, Q i ≤ P i`.

## What the decompositions rest on

The one-dimensional regrouping lemmas of `RegularityLemmata/Partition/Basic.lean` are not what
proves the box decompositions. Those follow from two facts about the product cells themselves —
distinct cells have disjoint tuple sets, and the cells cover `A.tuples` — after which a single
`Finset` biUnion sum splits the mass. Both decompositions are exact and **denominator-free**, so
they hold for signed weights and for boxes of zero mass, with no positivity anywhere.

## Not here

`CoordinateSplit` is not mentioned. Restriction and gluing along a split remain the separate
final tranche.
-/

namespace RegularityLemmata

variable {ι : Type*} {V : ι → Type*}

/-! ### Box partitions and their product cells -/

/-- **A partition of a box**: a `Finpartition` of the allowed values in each coordinate,
chosen independently. Unbundled, exactly as `FiniteBox` is.-/
abbrev BoxPartition [∀ i, DecidableEq (V i)] (A : FiniteBox V) : Type _ :=
  ∀ i, Finpartition (A i)

/-- **The product cells of a box partition**: the boxes obtained by choosing one part in each
coordinate. Built from Mathlib's dependent `piFinset`, the same enumeration `FiniteBox.tuples`
uses, rather than a second mechanism.-/
def boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] {A : FiniteBox V}
    (P : BoxPartition A) : Finset (FiniteBox V) :=
  Fintype.piFinset fun i => (P i).parts

/--
@isnad1 id=iff.0h5v.s6.aea3c93fafc7 from=translated src=- shape=4f4c67cc vocab=53d47c8e
-/
@[simp] theorem mem_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P : BoxPartition A} {C : FiniteBox V} :
    C ∈ boxCells P ↔ ∀ i, C i ∈ (P i).parts := Fintype.mem_piFinset

/-- **The number of product cells** is the product of the per-coordinate part counts.
@isnad1 id=eq.0h4v.s6.6cfd01ae853e from=translated src=- shape=95913ccd vocab=aabf3f59
-/
@[simp] theorem card_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) :
    (boxCells P).card = ∏ i, (P i).parts.card := Fintype.card_piFinset _

/-- Every product cell is a sub-box of the box being partitioned.
@isnad1 id=le.1h6v.s6.e4f9d09079dc from=translated src=- shape=06eeaf06 vocab=3ccd76d1
-/
theorem boxCells_subset [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] {A : FiniteBox V}
    {P : BoxPartition A} {C : FiniteBox V} (hC : C ∈ boxCells P) (i : ι) : C i ⊆ A i :=
  (P i).le (mem_boxCells.mp hC i)

/--
@isnad1 id=le.1h5v.s6.167adcc43172 from=translated src=- shape=588232d1 vocab=7822f264
-/
theorem tuples_subset_of_mem_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P : BoxPartition A} {C : FiniteBox V} (hC : C ∈ boxCells P) :
    C.tuples ⊆ A.tuples := fun _ hx =>
  FiniteBox.mem_tuples.mpr fun i => boxCells_subset hC i (FiniteBox.mem_tuples.mp hx i)

/-! ### The cell of a tuple -/

/-- The product cell a tuple lies in: coordinatewise, the part containing its value there.-/
def cellOf [∀ i, DecidableEq (V i)] {A : FiniteBox V} (P : BoxPartition A) (x : ∀ i, V i) :
    FiniteBox V := fun i => (P i).part (x i)

/--
@isnad1 id=eq.0h6v.s5.dc5599e24722 from=translated src=- shape=eeb6d6e3 vocab=b08b932e
-/
@[simp] theorem cellOf_apply [∀ i, DecidableEq (V i)] {A : FiniteBox V} (P : BoxPartition A)
    (x : ∀ i, V i) (i : ι) : cellOf P x i = (P i).part (x i) := rfl

/--
@isnad1 id=mem.1h5v.s6.74d1813e8192 from=translated src=- shape=3b0899ca vocab=576b5a11
-/
theorem cellOf_mem_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) {x : ∀ i, V i} (hx : x ∈ A.tuples) :
    cellOf P x ∈ boxCells P :=
  mem_boxCells.mpr fun i => (P i).part_mem.mpr (FiniteBox.mem_tuples.mp hx i)

/--
@isnad1 id=mem.1h5v.s6.8f225904cb9d from=translated src=- shape=aabd0cf2 vocab=ffed70f3
-/
theorem mem_tuples_cellOf [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) {x : ∀ i, V i} (hx : x ∈ A.tuples) :
    x ∈ (cellOf P x).tuples :=
  FiniteBox.mem_tuples.mpr fun i => (P i).mem_part (FiniteBox.mem_tuples.mp hx i)

/-- A tuple determines its cell: any cell containing it is the one `cellOf` names.-/
theorem eq_cellOf_of_mem_tuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P : BoxPartition A} {C : FiniteBox V} (hC : C ∈ boxCells P)
    {x : ∀ i, V i} (hx : x ∈ C.tuples) : C = cellOf P x := by
  funext i
  refine (P i).eq_of_mem_parts (mem_boxCells.mp hC i) ((P i).part_mem.mpr ?_)
    (FiniteBox.mem_tuples.mp hx i) ((P i).mem_part ?_)
  · exact boxCells_subset hC i (FiniteBox.mem_tuples.mp hx i)
  · exact boxCells_subset hC i (FiniteBox.mem_tuples.mp hx i)

/-! ### Disjointness and coverage -/

/-- **Distinct product cells have disjoint tuple sets.** They differ in some coordinate, and two
distinct parts there are disjoint.
@isnad1 id=pairwise.0h4v.s6.f5ed12426cf2 from=translated src=- shape=3e68eae5 vocab=368a3ebd
-/
theorem boxCells_pairwiseDisjoint [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) :
    ((boxCells P : Finset (FiniteBox V)) : Set (FiniteBox V)).PairwiseDisjoint
      FiniteBox.tuples := by
  intro C hC D hD hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro x hxC hxD
  exact hne ((eq_cellOf_of_mem_tuples (Finset.mem_coe.mp hC) hxC).trans
    (eq_cellOf_of_mem_tuples (Finset.mem_coe.mp hD) hxD).symm)

/-- **The product cells cover the box.**
@isnad1 id=eq.0h4v.s6.333238b8793b from=translated src=- shape=dd973bb7 vocab=4150d4f2
-/
theorem biUnion_boxCells_tuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) :
    (boxCells P).biUnion FiniteBox.tuples = A.tuples := by
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, hx⟩
    exact tuples_subset_of_mem_boxCells hC hx
  · intro hx
    exact ⟨cellOf P x, cellOf_mem_boxCells P hx, mem_tuples_cellOf P hx⟩

/-! ### Exact decompositions

Both are denominator-free and carry no positivity hypothesis, so they hold for signed weights
and for boxes of zero mass, including the case of an empty coordinate where every side is `0`. -/

/-- **The mass of a box is the sum of the masses of its product cells.**
@isnad1 id=eq.0h5v.s6.8908e64a99af from=translated src=- shape=8c39f050 vocab=a5d0800a
-/
theorem boxMass_eq_sum_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {A : FiniteBox V} (P : BoxPartition A) :
    boxMass w A = ∑ C ∈ boxCells P, boxMass w C := by
  rw [boxMass_apply, ← biUnion_boxCells_tuples P,
    Finset.sum_biUnion (boxCells_pairwiseDisjoint P)]
  rfl

/-- **Predicate mass decomposes the same way**, since the predicate cuts each cell
independently.
@isnad1 id=eq.0h6v.s6.9f906c8eaeb3 from=translated src=- shape=39e66498 vocab=578d4ff0
-/
theorem boxPredMass_eq_sum_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {A : FiniteBox V} (P : BoxPartition A) (p : (∀ i, V i) → Prop)
    [DecidablePred p] :
    boxPredMass w A p = ∑ C ∈ boxCells P, boxPredMass w C p := by
  rw [boxPredMass_apply, ← biUnion_boxCells_tuples P, Finset.filter_biUnion,
    Finset.sum_biUnion]
  · rfl
  · exact (boxCells_pairwiseDisjoint P).mono fun C => Finset.filter_subset _ _

/-! ### Reindexing -/

/-- Transporting a box partition along an equivalence of index types. The carrier matches
because `(A.reindex e) j` is `A (e j)` definitionally.-/
def BoxPartition.reindex [∀ i, DecidableEq (V i)] {ι' : Type*} (e : ι' ≃ ι) {A : FiniteBox V}
    (P : BoxPartition A) : BoxPartition (A.reindex e) := fun j => P (e j)

/--
@isnad1 id=eq.0h7v.s7.04f28ba3e30f from=translated src=- shape=c0c3b8da vocab=27ff7bdb
-/
@[simp] theorem BoxPartition.reindex_apply [∀ i, DecidableEq (V i)] {ι' : Type*} (e : ι' ≃ ι)
    {A : FiniteBox V} (P : BoxPartition A) (j : ι') : P.reindex e j = P (e j) := rfl

/-- **Reindexing carries the product cells across**, bijectively.
@isnad1 id=eq.0h6v.s8.d655f0b80cba from=translated src=- shape=4829c4de vocab=af434ff2
-/
theorem boxCells_reindex [Fintype ι] [DecidableEq ι] {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    [∀ i, DecidableEq (V i)] (e : ι' ≃ ι) {A : FiniteBox V} (P : BoxPartition A) :
    boxCells (P.reindex e) = (boxCells P).image (FiniteBox.reindex e) := by
  ext D
  simp only [mem_boxCells, Finset.mem_image]
  constructor
  · -- `fun i => D (e.symm i)` does not typecheck: its value lies in `V (e (e.symm i))`, not
    -- `V i`. The tuple equivalence is what supplies the transport.
    intro hD
    refine ⟨Equiv.piCongrLeft (fun i => Finset (V i)) e D, fun i => ?_, ?_⟩
    · rw [← Equiv.apply_symm_apply e i, Equiv.piCongrLeft_apply_apply]
      exact hD (e.symm i)
    · funext j
      rw [FiniteBox.reindex_apply, Equiv.piCongrLeft_apply_apply]
  · rintro ⟨C, hC, rfl⟩ j
    exact hC (e j)

/--
@isnad1 id=eq.0h6v.s7.66d8d35e80c9 from=translated src=- shape=094489bf vocab=1dfa9297
-/
theorem card_boxCells_reindex [Fintype ι] [DecidableEq ι] {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] [∀ i, DecidableEq (V i)] (e : ι' ≃ ι) {A : FiniteBox V}
    (P : BoxPartition A) : (boxCells (P.reindex e)).card = (boxCells P).card := by
  rw [card_boxCells, card_boxCells]
  exact Fintype.prod_equiv e _ _ fun _ => rfl

/-! ### Refinement

`Q ≤ P` coordinatewise means `Q` is the finer partition, following
`RegularityLemmata/Partition/Basic.lean`. -/

/-- **Every cell of a finer box partition sits inside exactly one cell of the coarser one.**
Uniqueness needs no extra hypothesis: parts of a `Finpartition` are nonempty, so a containing
part is pinned by any point of the finer cell.
@isnad1 id=existsun.2h6v.s7.d9cc60c1c6aa from=translated src=- shape=6b6db911 vocab=f899b11e
-/
theorem existsUnique_parent_boxCell [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P Q : BoxPartition A} (hQP : ∀ i, Q i ≤ P i) {D : FiniteBox V}
    (hD : D ∈ boxCells Q) : ∃! C : FiniteBox V, C ∈ boxCells P ∧ ∀ i, D i ⊆ C i := by
  classical
  have hchoice : ∀ i, ∃ C ∈ (P i).parts, D i ⊆ C := fun i => hQP i (mem_boxCells.mp hD i)
  refine ⟨fun i => (hchoice i).choose,
    ⟨mem_boxCells.mpr fun i => (hchoice i).choose_spec.1,
      fun i => (hchoice i).choose_spec.2⟩, ?_⟩
  rintro C' ⟨hC', hsub'⟩
  funext i
  obtain ⟨v, hv⟩ := (Q i).nonempty_of_mem_parts (mem_boxCells.mp hD i)
  exact (P i).eq_of_mem_parts (mem_boxCells.mp hC' i) (hchoice i).choose_spec.1 (hsub' i hv)
    ((hchoice i).choose_spec.2 hv)

/-! ### Tests -/

section Tests

/-- Genuinely different carrier types in the two coordinates.-/
private abbrev VP : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Fin 3

private instance : ∀ i, DecidableEq (VP i)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | 1 => inferInstanceAs (DecidableEq (Fin 3))

private def bxP : FiniteBox VP
  | 0 => Finset.univ
  | 1 => Finset.univ

/-- **Genuinely unequal coordinate partitions.** The first coordinate is left whole and the
second is cut into singletons, so the two coordinates are not partitioned alike.-/
private def mixedP : BoxPartition bxP
  | 0 => Finpartition.indiscrete (by decide)
  | 1 => ⊥

-- Three product cells: one part in the first coordinate, three in the second.

/-- A weight that is **signed** and **nonuniform** both across coordinates and within each
coordinate.-/
private def wP : ∀ i, VP i → ℝ
  | 0, v => if v = 0 then -2 else 1
  | 1, v => if v = 0 then 3 else -1

-- **Signed, nonuniform weights.** The decomposition is an exact splitting of a finite sum, so it
-- survives weights that are negative and vary within a coordinate.
private def fineP : BoxPartition bxP := fun _ => ⊥

end Tests

end RegularityLemmata
