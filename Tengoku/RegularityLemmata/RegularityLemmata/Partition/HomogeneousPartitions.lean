/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.HomogeneousPair
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneity of a partition pair

A pair of partitions is `ε`-homogeneous for `R` when **every** cell rectangle is: the
cellwise lift of `IsHomogeneousPair` to independent partitions of two heterogeneous carriers.

## One tolerance, not two

The tolerance is a single scalar. Homogeneity measures one rectangle density, so there is one
output tolerance; side asymmetry belongs in the *inputs* of a perturbation result, where the
degradation `cX + cY + 2·cX·cY` of `abs_pairDensity_sub_le_of_relative_grow` is itself
symmetric under swapping the carriers. Left/right output scalars would not express anything
natural here. Should genuinely variable tolerances be needed later, the honest generalization
is a **cell-pair schedule** `P.parts → Q.parts → ℝ`, not two scalars.

## Endpoints

The two extremes are exact rather than approximate, and both are proved here so consumers
need not re-derive them: `⊥` (all cells singletons) is homogeneous at tolerance `0`, and a
pair of indiscrete partitions is homogeneous exactly when the whole rectangle is.

Nothing in this file mentions ladders, trees, ranks, or any stability notion.
-/

namespace RegularityLemmata

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {R : α → β → Prop}
variable {A : Finset α} {B : Finset β} {ε ε' : ℝ}

/-- Every cell rectangle of the pair is `ε`-homogeneous.-/
def AreHomogeneousPartitions (R : α → β → Prop) {A : Finset α} {B : Finset β}
    (P : Finpartition A) (Q : Finpartition B) (ε : ℝ) : Prop :=
  ∀ p ∈ P.parts, ∀ q ∈ Q.parts, IsHomogeneousPair R p q ε

/-! ### Tolerance monotonicity -/

/--
@isnad1 id=arehomog.2h9v.s6.8a723bec10ec from=translated src=- shape=da5d10db vocab=a54f02c5
-/
theorem AreHomogeneousPartitions.mono {P : Finpartition A} {Q : Finpartition B}
    (h : AreHomogeneousPartitions R P Q ε) (hε : ε ≤ ε') :
    AreHomogeneousPartitions R P Q ε' :=
  fun p hp q hq ↦ (h p hp q hq).mono hε

/-! ### Transpose and complement

Both are inherited cellwise from the rectangle-level equivalences, so they are `iff`s rather
than one-way transports. -/

/-- Transposing exchanges the two partitions.
@isnad1 id=iff.0h8v.s6.e41b403615a2 from=translated src=- shape=5a6984b8 vocab=8efe118a
-/
theorem areHomogeneousPartitions_swapRel_iff {P : Finpartition A} {Q : Finpartition B} :
    AreHomogeneousPartitions (swapRel R) Q P ε ↔ AreHomogeneousPartitions R P Q ε := by
  constructor
  · intro h p hp q hq
    exact isHomogeneousPair_swapRel_iff.mp (h q hq p hp)
  · intro h q hq p hp
    exact isHomogeneousPair_swapRel_iff.mpr (h p hp q hq)

/-- Complementing the relation preserves homogeneity of the pair, empty cells included.
@isnad1 id=iff.0h8v.s6.9d7fb56af94d from=translated src=- shape=5927892e vocab=d27857c6
-/
theorem areHomogeneousPartitions_not_iff {P : Finpartition A} {Q : Finpartition B} :
    AreHomogeneousPartitions (fun a b => ¬ R a b) P Q ε ↔ AreHomogeneousPartitions R P Q ε := by
  constructor
  · intro h p hp q hq
    exact isHomogeneousPair_not_iff.mp (h p hp q hq)
  · intro h p hp q hq
    exact isHomogeneousPair_not_iff.mpr (h p hp q hq)

/-! ### Endpoints -/

/-- **The trivial tolerance.** At `1/2` every partition pair is homogeneous, for every
relation — the cellwise lift of `isHomogeneousPair_of_half_le`.
@isnad1 id=arehomog.1h8v.s6.39dd12eeff5a from=translated src=- shape=7158915a vocab=f4783d85
-/
theorem areHomogeneousPartitions_of_half_le (R : α → β → Prop) (P : Finpartition A)
    (Q : Finpartition B) (hε : (1 : ℝ) / 2 ≤ ε) : AreHomogeneousPartitions R P Q ε :=
  fun p _ q _ ↦ isHomogeneousPair_of_half_le R p q hε

/-- **The bottom partitions are exactly homogeneous.** Every cell of `⊥` is a singleton, so
every cell rectangle is a one-point rectangle with density `0` or `1`. This needs tolerance
`0`, not a positive one.
@isnad1 id=arehomog.0h5v.s6.1b6c59abff19 from=translated src=- shape=5a87896c vocab=60a0b111
-/
theorem areHomogeneousPartitions_bot (R : α → β → Prop) :
    AreHomogeneousPartitions R (⊥ : Finpartition A) (⊥ : Finpartition B) 0 := by
  intro p hp q hq
  rw [Finpartition.parts_bot, Finset.mem_map] at hp hq
  obtain ⟨a, -, rfl⟩ := hp
  obtain ⟨b, -, rfl⟩ := hq
  exact isHomogeneousPair_singleton R a b

/-- …hence at every nonnegative tolerance.
@isnad1 id=arehomog.1h6v.s6.b87cf6f0a126 from=translated src=- shape=cf9ffe7d vocab=466616b0
-/
theorem areHomogeneousPartitions_bot_of_nonneg (R : α → β → Prop) (hε : 0 ≤ ε) :
    AreHomogeneousPartitions R (⊥ : Finpartition A) (⊥ : Finpartition B) ε :=
  (areHomogeneousPartitions_bot R).mono hε

/-- **The indiscrete pair is the whole rectangle.** With one cell on each side, homogeneity of
the pair is exactly homogeneity of `A ×ˢ B`.
@isnad1 id=iff.2h6v.s6.7c02f7ea01ca from=translated src=- shape=410f7b6b vocab=b3a44e1a
-/
theorem areHomogeneousPartitions_indiscrete_iff {hA : A ≠ ∅} {hB : B ≠ ∅} :
    AreHomogeneousPartitions R (Finpartition.indiscrete hA) (Finpartition.indiscrete hB) ε
      ↔ IsHomogeneousPair R A B ε := by
  constructor
  · intro h
    exact h A (by rw [Finpartition.indiscrete_parts]; exact Finset.mem_singleton_self _)
      B (by rw [Finpartition.indiscrete_parts]; exact Finset.mem_singleton_self _)
  · intro h p hp q hq
    rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hp hq
    subst hp; subst hq
    exact h

/-! ### Tests -/

section Tests

-- **A single tolerance is genuinely one number**: the same `ε` bounds every cell pair, on
-- carriers of different sizes with independent partitions.

end Tests

end RegularityLemmata
