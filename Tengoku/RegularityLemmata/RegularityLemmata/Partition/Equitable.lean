/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Basic
import Tengoku.Seed.Order.Partition.Equipartition
import Tengoku.Seed.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cell splitting and equitable partitions

Within-cell splitting: `twoPartition` splits one finset into a nonempty subset and its
complement, and `refineBySplit` refines a partition by splitting a single part —
adding exactly one part (the elementary step of energy-increment iterations).

Chunking, remainder distribution, and balanced splitting are mathlib's
`Finpartition.equitabilise` / `Finpartition.IsEquipartition`; this file only re-exports
the two facts the almost-refinement layer consumes (part sizes in `{m, m+1}` and the
per-parent uncovered remainder bound `Finpartition.card_parts_equitabilise_subset_le`)
plus `Finpartition.exists_equipartition_card_eq`. Size bounds for equipartitions are
`Finpartition.IsEquipartition.average_le_card_part` / `card_part_le_average_add_one`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-! ### Splitting one cell -/

/-- Split a cell `C` into `A` and `C \ A`, producing a two-part partition of `C`.-/
def twoPartition (C A : Finset α) (hA : A ⊆ C)
    (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) : Finpartition C :=
  (Finpartition.indiscrete (Finset.Nonempty.ne_empty hAne)).extend
    (Finset.Nonempty.ne_empty hBne)
    disjoint_sdiff_self_right
    (Finset.union_sdiff_of_subset hA)

/-- The two-part partition has exactly 2 parts.
@isnad1 id=eq.3h3v.s6.585802a51f73 from=translated src=- shape=0b5b67de vocab=916c663f
-/
theorem twoPartition_card {C A : Finset α} {hA : A ⊆ C}
    {hAne : A.Nonempty} {hBne : (C \ A).Nonempty} :
    (twoPartition C A hA hAne hBne).parts.card = 2 := by
  unfold twoPartition
  rw [Finpartition.card_extend, Finpartition.indiscrete_parts, Finset.card_singleton]

/-- Refine a partition by splitting the part `C` into `A` and `C \ A`.-/
def refineBySplit (P : Finpartition s) (C : Finset α) (_hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    Finpartition s :=
  P.bind (fun D hD =>
    if h : D = C then h ▸ twoPartition C A hA hAne hBne
    else Finpartition.indiscrete (by rintro rfl; exact absurd hD P.bot_notMem))

/-- The refined partition refines (`≤`) the original.
@isnad1 id=le.4h5v.s6.9819bc7d8292 from=translated src=- shape=570c3252 vocab=bd132dd0
-/
theorem refineBySplit_le (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    refineBySplit P C hC A hA hAne hBne ≤ P := by
  intro b hb
  simp only [refineBySplit, Finpartition.mem_bind] at hb
  obtain ⟨D, hD, hb'⟩ := hb
  refine ⟨D, hD, ?_⟩
  set Q : Finpartition D := if h : D = C then h ▸ twoPartition C A hA hAne hBne
    else Finpartition.indiscrete (by rintro rfl; exact absurd hD P.bot_notMem) with hQ_def
  have hb_mem : b ∈ Q.parts := by convert hb'
  exact Q.le hb_mem

/-- Splitting one part adds exactly one part.
@isnad1 id=eq.4h5v.s7.b7b280788da0 from=translated src=- shape=31056f66 vocab=5b0b0cc3
-/
theorem refineBySplit_parts_card_eq (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    (refineBySplit P C hC A hA hAne hBne).parts.card = P.parts.card + 1 := by
  simp only [refineBySplit, Finpartition.card_bind]
  set S := P.parts.attach
  set x₀ : { x // x ∈ P.parts } := ⟨C, hC⟩
  set f : { x // x ∈ P.parts } → ℕ := fun D =>
    (if h : D.1 = C then h ▸ twoPartition C A hA hAne hBne
     else Finpartition.indiscrete
      (show D.1 ≠ ⊥ by intro h; exact absurd (h ▸ D.2) P.bot_notMem)).parts.card
  have hx₀ : x₀ ∈ S := Finset.mem_attach _ _
  rw [show ∑ D ∈ S, _ = ∑ D ∈ S, f D from Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [← Finset.add_sum_erase S f hx₀]
  have hC_term : f x₀ = 2 := by simp [f, x₀, twoPartition_card]
  rw [hC_term]
  have hrest : ∀ D ∈ S.erase x₀, f D = 1 := by
    intro ⟨D, hD⟩ hmem
    have hne : D ≠ C := by
      intro heq; exact (Finset.mem_erase.mp hmem).1 (Subtype.ext heq)
    simp [f, hne, Finpartition.indiscrete_parts]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const]
  have hcard_erase : (S.erase x₀).card = P.parts.card - 1 := by
    rw [Finset.card_erase_of_mem hx₀, Finset.card_attach]
  rw [hcard_erase]
  have hpos : 0 < P.parts.card := Finset.card_pos.mpr ⟨C, hC⟩
  simp; omega

/-- Splitting one part adds at most one part.
@isnad1 id=le.4h5v.s7.30685a4c00fd from=translated src=- shape=4b040294 vocab=5b0b0cc3
-/
theorem refineBySplit_parts_card_le (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    (refineBySplit P C hC A hA hAne hBne).parts.card ≤ P.parts.card + 1 :=
  (refineBySplit_parts_card_eq P C hC A hA hAne hBne).le

/-! ### Exact characterizations of the split -/

/-- The two-part partition consists of exactly `A` and `C \ A`.
@isnad1 id=eq.3h3v.s6.1dc473d75014 from=translated src=- shape=f80c4d16 vocab=ac407f43
-/
theorem twoPartition_parts {C A : Finset α} {hA : A ⊆ C} {hAne : A.Nonempty}
    {hBne : (C \ A).Nonempty} :
    (twoPartition C A hA hAne hBne).parts = {A, C \ A} := by
  rw [twoPartition, Finpartition.extend_parts, Finpartition.indiscrete_parts,
    Finset.pair_comm]

/-- Exact parts formula for the one-cell split.
@isnad1 id=eq.4h5v.s7.982819e4c02e from=translated src=- shape=66e30fd7 vocab=7f5837f1
-/
theorem refineBySplit_parts (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    (refineBySplit P C hC A hA hAne hBne).parts = (P.parts.erase C) ∪ {A, C \ A} := by
  ext b
  simp only [refineBySplit, Finpartition.mem_bind, Finset.mem_union, Finset.mem_erase,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨D, hD, hb⟩
    by_cases h : D = C
    · subst h
      rw [dite_eq_left rfl] at hb
      have hb' : b ∈ (twoPartition D A hA hAne hBne).parts := hb
      rw [twoPartition_parts, Finset.mem_insert, Finset.mem_singleton] at hb'
      exact Or.inr hb'
    · rw [dite_eq_right h, Finpartition.indiscrete_parts, Finset.mem_singleton] at hb
      subst hb
      exact Or.inl ⟨h, hD⟩
  · rintro (⟨hbC, hbP⟩ | hb)
    · refine ⟨b, hbP, ?_⟩
      rw [dite_eq_right hbC, Finpartition.indiscrete_parts, Finset.mem_singleton]
    · refine ⟨C, hC, ?_⟩
      rw [dite_eq_left rfl]
      show b ∈ (twoPartition C A hA hAne hBne).parts
      rw [twoPartition_parts, Finset.mem_insert, Finset.mem_singleton]
      exact hb

/-- Membership in the split partition.
@isnad1 id=iff.4h6v.s7.1f0fc30b8a95 from=translated src=- shape=02133adc vocab=bd132dd0
-/
theorem mem_refineBySplit {P : Finpartition s} {C : Finset α} {hC : C ∈ P.parts}
    {A : Finset α} {hA : A ⊆ C} {hAne : A.Nonempty} {hBne : (C \ A).Nonempty}
    {b : Finset α} :
    b ∈ (refineBySplit P C hC A hA hAne hBne).parts ↔
      (b ∈ P.parts ∧ b ≠ C) ∨ b = A ∨ b = C \ A := by
  rw [refineBySplit_parts, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_singleton, and_comm]

/-- The split pieces are parts of the split partition.
@isnad1 id=mem.4h5v.s6.a0204f4334e3 from=translated src=- shape=21971204 vocab=bd132dd0
-/
theorem left_mem_refineBySplit {P : Finpartition s} {C : Finset α} (hC : C ∈ P.parts)
    {A : Finset α} (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    A ∈ (refineBySplit P C hC A hA hAne hBne).parts :=
  mem_refineBySplit.mpr (Or.inr (Or.inl rfl))

/--
@isnad1 id=mem.4h5v.s6.ce8e261bf18a from=translated src=- shape=829d46f7 vocab=bd132dd0
-/
theorem sdiff_mem_refineBySplit {P : Finpartition s} {C : Finset α} (hC : C ∈ P.parts)
    {A : Finset α} (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    C \ A ∈ (refineBySplit P C hC A hA hAne hBne).parts :=
  mem_refineBySplit.mpr (Or.inr (Or.inr rfl))

/-- Every part other than the split one survives untouched.
@isnad1 id=mem.6h6v.s7.7a16da474702 from=translated src=- shape=62587fcf vocab=bd132dd0
-/
theorem mem_refineBySplit_of_ne {P : Finpartition s} {C : Finset α} (hC : C ∈ P.parts)
    {A : Finset α} (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty)
    {D : Finset α} (hD : D ∈ P.parts) (hne : D ≠ C) :
    D ∈ (refineBySplit P C hC A hA hAne hBne).parts :=
  mem_refineBySplit.mpr (Or.inl ⟨hD, hne⟩)

/-! ### Equitabilise re-exports

The consumers below are `RegularityLemmata/Partition/AlmostRefines.lean` and the graph ladder. -/

variable {a b m : ℕ} {P : Finpartition s}

/-- Part sizes of an equitabilisation lie in `{m, m + 1}`
(mathlib's `Finpartition.card_eq_of_mem_parts_equitabilise`).
@isnad1 id=or.2h7v.s7.80a83b33d3d5 from=translated src=- shape=4a7dc50d vocab=2f502408
-/
theorem equitabilise_card_part {h : a * m + b * (m + 1) = s.card} {t : Finset α}
    (ht : t ∈ (P.equitabilise h).parts) : t.card = m ∨ t.card = m + 1 :=
  Finpartition.card_eq_of_mem_parts_equitabilise ht

/-- The uncovered remainder of each original part has size at most `m`
(mathlib's `Finpartition.card_parts_equitabilise_subset_le`, restated with
`Finset.filter`). This is the primitive behind `AlmostRefinesAt`.
@isnad1 id=le.2h7v.s7.66124927e023 from=translated src=- shape=2b480015 vocab=f71064ab
-/
theorem equitabilise_uncovered_card_le {h : a * m + b * (m + 1) = s.card} {t : Finset α}
    (ht : t ∈ P.parts) :
    (t \ ((P.equitabilise h).parts.filter (· ⊆ t)).biUnion id).card ≤ m :=
  P.card_parts_equitabilise_subset_le (h := h) ht

/-- **Equipartition part-size bound.** Every cell of an equipartition has cardinality at most
`|s| / #parts + 1`.
@isnad1 id=le.2h4v.s6.73d8f867acc2 from=translated src=- shape=aaa77b48 vocab=edf2b6f3
-/
theorem forall_card_le_of_isEquipartition (hP : P.IsEquipartition) :
    ∀ B ∈ P.parts, B.card ≤ s.card / P.parts.card + 1 :=
  fun _ hB => hP.card_part_le_average_add_one hB

/-! ### Tests and adversarial examples -/

-- `twoPartition` on an explicit 4-element finset.

end RegularityLemmata
