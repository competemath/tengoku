/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Equitable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Grouping the cells of a partition into owners

`ARCHITECTURE.md` route (b) ladder step 2 (grouping frozen 2026-07-28). Proxy cells are
obtained by GROUPING the cells of an already-regular equipartition into owners, never by
splitting a regular cell. This file supplies the grouping itself, at the level of an
arbitrary `Finpartition`:

* `groupUnion Q g j` — the union of the cells labeled `j` by `g`. An owner is such a
  union; its proxies are the cells in the fiber.
* `groupUnion_disjoint`, `biUnion_groupUnion` — owners with distinct labels are disjoint,
  and the owners of all labels used cover the ground set exactly. Together these say the
  owners partition `s` (`groupUnion_isPartUnion` records that each is a part union, which
  is what the refinement API consumes).
* `card_groupUnion` — an owner's cardinality is the SUM of its proxies' cardinalities,
  since distinct cells are disjoint.
* `card_groupUnion_bounds` — from an equipartition with cells of size `m` or `m + 1` and a
  fiber of exactly `d` cells: `d·m ≤ |owner| ≤ d·m + d`. At `d = 3` this is the frozen
  `3m ≤ |owner| ≤ 3m + 3`, and the intermediate values are ordinary mixed triples.
* `exists_fiber_labeling` — the construction: any finset of cardinality `d·k` admits a
  labeling by `Fin k`-many labels whose every fiber has EXACTLY `d` elements. With
  `d = 3` and `3 ∣ #Q.parts` — which `RegularityLemmata/Graph/TripleSeed.lean` arranges — this
  produces the owner labeling.

Everything is stated for a general fiber size `d`; the route fixes `d = 3`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-! ### A labeling with fibers of a fixed size -/

/-- **The grouping construction.** A finset of cardinality `d · k` admits a labeling whose
every fiber below `k` has exactly `d` elements. Applied to `Q.parts` with `d = 3`, this is
the owner labeling: each owner is a fiber of three cells.
@isnad1 id=ex.1h4v.s6.1f73a0c87441 from=translated src=- shape=5056fbb3 vocab=14a0ff41
-/
theorem exists_fiber_labeling {β : Type*} [DecidableEq β] (d : ℕ) :
    ∀ (k : ℕ) (S : Finset β), S.card = d * k →
      ∃ g : β → ℕ, (∀ x ∈ S, g x < k) ∧
        ∀ j < k, (S.filter fun x => g x = j).card = d := by
  intro k
  induction k with
  | zero =>
    intro S hS
    rw [Nat.mul_zero, Finset.card_eq_zero] at hS
    exact ⟨fun _ => 0, by simp [hS], by omega⟩
  | succ k IH =>
    intro S hS
    have hdS : d ≤ S.card := by
      rw [hS]
      exact Nat.le_mul_of_pos_right d (Nat.succ_pos k)
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hdS
    have hrest : (S \ T).card = d * k := by
      rw [Finset.card_sdiff_of_subset hTS, hS, hTcard, Nat.mul_succ, Nat.add_sub_cancel]
    obtain ⟨g', hg'lt, hg'fib⟩ := IH (S \ T) hrest
    classical
    refine ⟨fun x => if x ∈ T then k else g' x, fun x hx => ?_, fun j hj => ?_⟩
    · by_cases hxT : x ∈ T
      · simp [hxT]
      · have := hg'lt x (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)
        simp [hxT]
        omega
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | rfl
      · have hfil : (S.filter fun x => (if x ∈ T then k else g' x) = j)
            = (S \ T).filter fun x => g' x = j := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · rintro ⟨hxS, hxg⟩
            by_cases hxT : x ∈ T
            · rw [ite_eq_left hxT] at hxg; omega
            · rw [ite_eq_right hxT] at hxg; exact ⟨⟨hxS, hxT⟩, hxg⟩
          · rintro ⟨⟨hxS, hxT⟩, hxg⟩
            exact ⟨hxS, by rw [ite_eq_right hxT]; exact hxg⟩
        rw [hfil]
        exact hg'fib j hjk
      · have hfil : (S.filter fun x => (if x ∈ T then j else g' x) = j) = T := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hxS, hxg⟩
            by_cases hxT : x ∈ T
            · exact hxT
            · rw [ite_eq_right hxT] at hxg
              have := hg'lt x (Finset.mem_sdiff.mpr ⟨hxS, hxT⟩)
              omega
          · intro hxT
            exact ⟨hTS hxT, by rw [ite_eq_left hxT]⟩
        rw [hfil, hTcard]

/-! ### Owners as unions of their proxies -/

/-- The union of the cells labeled `j`: an OWNER, whose proxies are the cells in the
fiber.-/
def groupUnion (Q : Finpartition s) (g : Finset α → ℕ) (j : ℕ) : Finset α :=
  (Q.parts.filter fun C => g C = j).biUnion id

variable {Q : Finpartition s} {g : Finset α → ℕ} {j j' : ℕ}

/--
@isnad1 id=le.0h5v.s5.e72caff4e6f6 from=translated src=- shape=89db0f91 vocab=ea83a9be
-/
theorem groupUnion_subset : groupUnion Q g j ⊆ s := by
  refine Finset.biUnion_subset.mpr fun C hC => ?_
  simpa using Q.le (Finset.mem_filter.mp hC).1

/-- A proxy sits inside its owner.
@isnad1 id=le.2h6v.s6.e477656039aa from=translated src=- shape=2d1f3ca7 vocab=ccdee3d8
-/
theorem subset_groupUnion {C : Finset α} (hC : C ∈ Q.parts) (hg : g C = j) :
    C ⊆ groupUnion Q g j := fun _ hx =>
  Finset.mem_biUnion.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hg⟩, hx⟩

/-- **Owners with distinct labels are disjoint**, because their proxies are distinct cells
of `Q`.
@isnad1 id=disjoint.1h6v.s5.06767501eae9 from=translated src=- shape=2fa53e7c vocab=b0bbf22b
-/
theorem groupUnion_disjoint (hjj : j ≠ j') :
    Disjoint (groupUnion Q g j) (groupUnion Q g j') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [groupUnion, Finset.mem_biUnion] at hx hx'
  obtain ⟨C, hC, hxC⟩ := hx
  obtain ⟨D, hD, hxD⟩ := hx'
  rw [Finset.mem_filter] at hC hD
  have hCD : C = D := Q.eq_of_mem_parts hC.1 hD.1 hxC hxD
  exact hjj (hC.2 ▸ hCD ▸ hD.2.symm ▸ rfl)

/-- Each owner is a union of `Q`-cells, hence a part union — the form the refinement API
consumes.
@isnad1 id=ispartun.0h5v.s5.c9c53fe05bee from=translated src=- shape=9d94d06b vocab=870e31f5
-/
theorem groupUnion_isPartUnion : IsPartUnion Q (groupUnion Q g j) := by
  refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Finset.mem_biUnion] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    exact (Finset.mem_filter.mp hC).2 hxC
  · rw [groupUnion, Finset.mem_biUnion] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    rw [Finset.mem_biUnion]
    exact ⟨C, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).1,
      subset_groupUnion (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hC).2⟩, hxC⟩

/-- **The owners cover the ground set exactly**: every vertex lies in the owner of its own
cell's label.
@isnad1 id=eq.1h5v.s6.3158a9e51368 from=translated src=- shape=af956b15 vocab=c4ad5d1d
-/
theorem biUnion_groupUnion (L : Finset ℕ) (hL : ∀ C ∈ Q.parts, g C ∈ L) :
    L.biUnion (groupUnion Q g) = s := by
  refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Finset.mem_biUnion] at hx
    obtain ⟨j, -, hxj⟩ := hx
    exact groupUnion_subset hxj
  · obtain ⟨C, hC, hxC⟩ := Q.exists_mem hx
    exact Finset.mem_biUnion.mpr ⟨g C, hL C hC, subset_groupUnion hC rfl hxC⟩

/-- **An owner's cardinality is the sum of its proxies'**, the cells being disjoint.
@isnad1 id=eq.0h5v.s6.b781e21f55ac from=translated src=- shape=cca09371 vocab=83825a87
-/
theorem card_groupUnion :
    (groupUnion Q g j).card = ∑ C ∈ Q.parts.filter fun C => g C = j, C.card := by
  rw [groupUnion, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun C _ => rfl
  · intro C hC D hD hCD
    exact Q.disjoint (Finset.mem_coe.mpr (Finset.mem_filter.mp hC).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hD).1) hCD

/-- **The frozen owner-size range.** From an equipartition whose cells have `m` or `m + 1`
elements and a fiber of exactly `d` cells: `d·m ≤ |owner| ≤ d·m + d`. At `d = 3` this is
`3m ≤ |owner| ≤ 3m + 3`; the intermediate values arise from mixed fibers and are ordinary,
so a size floor must be stated against the RANGE. (Only the cell-size sandwich is used, so
the equipartition hypothesis is not restated here — `card_part_bounds` supplies it.)
@isnad1 id=and.2h7v.s7.9f0340b7edf8 from=translated src=- shape=ad62de7c vocab=0e2eb564
-/
theorem card_groupUnion_bounds {m d : ℕ}
    (hm : ∀ C ∈ Q.parts, m ≤ C.card ∧ C.card ≤ m + 1)
    (hfib : (Q.parts.filter fun C => g C = j).card = d) :
    d * m ≤ (groupUnion Q g j).card ∧ (groupUnion Q g j).card ≤ d * m + d := by
  rw [card_groupUnion]
  constructor
  · calc d * m = ∑ _C ∈ Q.parts.filter fun C => g C = j, m := by
          rw [Finset.sum_const, hfib, smul_eq_mul]
      _ ≤ ∑ C ∈ Q.parts.filter fun C => g C = j, C.card :=
          Finset.sum_le_sum fun C hC => (hm C (Finset.mem_filter.mp hC).1).1
  · calc ∑ C ∈ Q.parts.filter fun C => g C = j, C.card
        ≤ ∑ _C ∈ Q.parts.filter fun C => g C = j, (m + 1) :=
          Finset.sum_le_sum fun C hC => (hm C (Finset.mem_filter.mp hC).1).2
      _ = d * m + d := by rw [Finset.sum_const, hfib, smul_eq_mul, Nat.mul_succ]

/-- The route's instance: three proxies per owner.
@isnad1 id=and.2h6v.s7.52006bbecb26 from=translated src=- shape=850cb117 vocab=0e2eb564
-/
theorem card_groupUnion_triple_bounds {m : ℕ}
    (hm : ∀ C ∈ Q.parts, m ≤ C.card ∧ C.card ≤ m + 1)
    (hfib : (Q.parts.filter fun C => g C = j).card = 3) :
    3 * m ≤ (groupUnion Q g j).card ∧ (groupUnion Q g j).card ≤ 3 * m + 3 :=
  card_groupUnion_bounds hm hfib

/-- **The bridge from divisibility to the owner labeling.** `3 ∣ #Q.parts` — which
`RegularityLemmata/Graph/TripleSeed.lean`'s seeded summit delivers — directly produces the owner
count `k` and a labeling whose every fiber is exactly a triple of cells. Downstream selection
consumes
this, rather than recomposing the divisibility and the labeling itself.
@isnad1 id=ex.1h3v.s7.9666e6b0d43f from=translated src=- shape=4253ad44 vocab=4f5c0b8c
-/
theorem exists_triple_grouping (h : 3 ∣ Q.parts.card) :
    ∃ k, ∃ g : Finset α → ℕ, Q.parts.card = 3 * k ∧
      (∀ C ∈ Q.parts, g C < k) ∧
      ∀ j < k, (Q.parts.filter fun C => g C = j).card = 3 := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨g, hglt, hgfib⟩ := exists_fiber_labeling 3 k Q.parts hk
  exact ⟨k, g, hk, hglt, hgfib⟩

/-! ### Tests and adversarial examples -/

section Tests

-- A labeling with fibers of size three exists on any six-element finset.

end Tests

end RegularityLemmata
