/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.RootSum
import Tengoku.Roundedrootsums.RoundedRootSums.MainFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nearest-integer square-root sums

This module defines square roots rounded to the nearest integer,
the corresponding rounding bonuses, and closed formulas for their finite sums.
-/

open scoped BigOperators

namespace RoundedRootSums

/--
The integer square root of `k`, rounded to the nearest integer.

Ties are rounded upward.-/
def nearestSqrt (k : Nat) : Nat :=
  let m := Nat.sqrt k
  if 2 * k < 2 * m ^ 2 + 2 * m + 1 then
    m
  else
    m + 1

/--
The sum of nearest-integer square roots from `1` through `n`.-/
def nearestRootSum (n : Nat) : Nat :=
  Finset.sum (Finset.range n) (fun k => nearestSqrt (k + 1))

/--
Unfolding the definition of the nearest-root sum.-/
theorem nearestRootSum_unfold (n : Nat) :
    nearestRootSum n =
      Finset.sum (Finset.range n)
        (fun k => nearestSqrt (k + 1)) := by
  rfl

/--
If the midpoint test fails, the nearest square root equals the floor.-/
theorem nearestSqrt_eq_floor
    (k : Nat)
    (h : 2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1) :
    nearestSqrt k = Nat.sqrt k := by
  simp [nearestSqrt, h]

/--
If the midpoint test succeeds, the nearest square root is one larger
than the floor.-/
theorem nearestSqrt_eq_succ
    (k : Nat)
    (h : ¬ 2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1) :
    nearestSqrt k = Nat.sqrt k + 1 := by
  simp [nearestSqrt, h]

/--
The nearest integer square root is either the floor or its successor.-/
theorem nearestSqrt_eq_floor_or_succ (k : Nat) :
    nearestSqrt k = Nat.sqrt k ∨
      nearestSqrt k = Nat.sqrt k + 1 := by
  by_cases h :
      2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1
  · left
    exact nearestSqrt_eq_floor k h
  · right
    exact nearestSqrt_eq_succ k h

/--
The nearest integer square root is never smaller than the floor.-/
theorem sqrt_le_nearestSqrt (k : Nat) :
    Nat.sqrt k ≤ nearestSqrt k := by
  rcases nearestSqrt_eq_floor_or_succ k with h | h
  · rw [h]
  · rw [h]
    omega

/--
The nearest integer square root never exceeds the successor of the floor.-/
theorem nearestSqrt_le_sqrt_add_one (k : Nat) :
    nearestSqrt k ≤ Nat.sqrt k + 1 := by
  rcases nearestSqrt_eq_floor_or_succ k with h | h
  · rw [h]
    omega
  · rw [h]

/--
The additional unit contributed when the square root is rounded upward.-/
def nearestBonus (k : Nat) : Nat :=
  if 2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1 then
    0
  else
    1

/--
Predicate expressing that the square root is rounded upward.-/
def roundsUp (k : Nat) : Prop :=
  ¬ 2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1

theorem roundsUp_iff (k : Nat) :
    roundsUp k ↔
      ¬ (2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1) := by
  unfold roundsUp
  rfl

instance roundsUpDecidable (k : Nat) : Decidable (roundsUp k) := by
  unfold roundsUp
  infer_instance

/--
The nearest square root equals the floor plus the rounding bonus.-/
theorem nearestSqrt_eq_sqrt_add_bonus (k : Nat) :
    nearestSqrt k = Nat.sqrt k + nearestBonus k := by
  by_cases h :
      2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1
  · rw [nearestSqrt_eq_floor k h]
    unfold nearestBonus
    simp [h]
  · rw [nearestSqrt_eq_succ k h]
    unfold nearestBonus
    simp [h]

/--
The rounding bonus is the indicator of the upward-rounding predicate.-/
theorem nearestBonus_eq_indicator (k : Nat) :
    nearestBonus k =
      if roundsUp k then 1 else 0 := by
  unfold nearestBonus roundsUp
  by_cases h :
      2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1
  · simp [h]
  · simp [h]

/--
The total number of upward-rounding bonuses among
the integers from `1` through `n`.-/
def nearestBonusSum (n : Nat) : Nat :=
  Finset.sum (Finset.range n)
    (fun k => nearestBonus (k + 1))

theorem nearestBonusSum_unfold (n : Nat) :
    nearestBonusSum n =
      Finset.sum (Finset.range n) (fun k => nearestBonus (k + 1)) := by
  rfl

/--
Indices `k = 0, ..., n - 1` for which the original integer
`k + 1` is rounded upward.-/
def roundedUpIndices (n : Nat) : Finset Nat :=
  (Finset.range n).filter
    (fun k => roundsUp (k + 1))

theorem mem_roundedUpIndices_iff (n k : Nat) :
    k ∈ roundedUpIndices n ↔
      k < n ∧ roundsUp (k + 1) := by
  simp [roundedUpIndices]

theorem roundsUp_not (k : Nat) :
    ¬ roundsUp k ↔
      2 * k < 2 * Nat.sqrt k ^ 2 + 2 * Nat.sqrt k + 1 := by
  unfold roundsUp
  tauto

theorem roundsUp_square_add_iff
    (m t : Nat)
    (ht : t ≤ 2 * m) :
    roundsUp (m ^ 2 + t) ↔ m + 1 ≤ t := by
  unfold roundsUp
  have hsqrt : Nat.sqrt (m ^ 2 + t) = m := by
    apply Nat.sqrt_add_eq'
    omega
  rw [hsqrt]
  omega

theorem roundsUp_square_add_iff'
    (m t : Nat)
    (ht : t ≤ 2 * m) :
    roundsUp (m ^ 2 + t) =
      (m + 1 ≤ t) := by
  apply propext
  exact roundsUp_square_add_iff m t ht

def roundedUpOffsets (m : Nat) : Finset Nat :=
  (Finset.range (2 * m + 1)).filter
    (fun t => roundsUp (m ^ 2 + t))

theorem mem_roundedUpOffsets_iff (m t : Nat) :
    t ∈ roundedUpOffsets m ↔
      t < 2 * m + 1 ∧ m + 1 ≤ t := by
  unfold roundedUpOffsets
  rw [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨ht, hup⟩
    have ht' : t ≤ 2 * m := by
      exact Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using ht)
    constructor
    · exact Finset.mem_range.mp ht
    · exact (roundsUp_square_add_iff m t ht').mp hup
  · intro h
    rcases h with ⟨ht, hup⟩
    have ht' : t ≤ 2 * m := by
      exact Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using ht)
    constructor
    · exact Finset.mem_range.mpr ht
    · exact (roundsUp_square_add_iff m t ht').mpr hup

theorem roundedUpOffsets_eq_Icc (m : Nat) :
    roundedUpOffsets m = Finset.Icc (m + 1) (2 * m) := by
  ext t
  rw [mem_roundedUpOffsets_iff]
  simp only [Finset.mem_Icc]
  omega

theorem roundedUpOffsets_card (m : Nat) :
    (roundedUpOffsets m).card = m := by
  rw [roundedUpOffsets_eq_Icc]
  simp
  omega

theorem not_roundsUp_square (m : Nat) :
    ¬ roundsUp (m ^ 2) := by
  unfold roundsUp
  simp [Nat.sqrt_eq']

theorem roundedUpIndices_square_succ_split
    (m : Nat) :
    roundedUpIndices ((m + 1) ^ 2) =
      roundedUpIndices (m ^ 2) ∪
        Finset.image
          (fun t => m ^ 2 + t - 1)
          (roundedUpOffsets m) := by
  ext k
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hk
    have hk' :
        k < (m + 1) ^ 2 ∧ roundsUp (k + 1) :=
      (mem_roundedUpIndices_iff ((m + 1) ^ 2) k).mp hk
    rcases hk' with ⟨hklt, hup⟩
    by_cases hsmall : k < m ^ 2
    · left
      exact
        (mem_roundedUpIndices_iff (m ^ 2) k).mpr
          ⟨hsmall, hup⟩
    · right
      let t : Nat := k + 1 - m ^ 2
      have hsquare :
          (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by
        ring
      have hmle : m ^ 2 ≤ k := by
        exact Nat.le_of_not_gt hsmall
      have ht_eq :
          m ^ 2 + t = k + 1 := by
        dsimp [t]
        omega
      have hk1le :
          k + 1 ≤ (m + 1) ^ 2 := by
        omega
      have hnot_square :
          ¬ roundsUp ((m + 1) ^ 2) :=
        not_roundsUp_square (m + 1)
      have hk1ne :
          k + 1 ≠ (m + 1) ^ 2 := by
        intro heq
        apply hnot_square
        rw [← heq]
        exact hup
      have hk1lt :
          k + 1 < (m + 1) ^ 2 := by
        omega
      have hklt' :
          k + 1 ≤ m ^ 2 + 2 * m := by
        rw [hsquare] at hk1lt
        omega
      have ht_le : t ≤ 2 * m := by
        dsimp [t]
        omega
      have hup_t :
          roundsUp (m ^ 2 + t) := by
        rw [ht_eq]
        exact hup
      have ht_lower : m + 1 ≤ t :=
        (roundsUp_square_add_iff m t ht_le).mp hup_t
      have ht_mem :
          t ∈ roundedUpOffsets m := by
        apply (mem_roundedUpOffsets_iff m t).mpr
        constructor
        · omega
        · exact ht_lower
      refine ⟨t, ht_mem, ?_⟩
      dsimp [t]
      omega
  · intro hk
    rcases hk with hk | hk
    · have hk' :
          k < m ^ 2 ∧ roundsUp (k + 1) :=
        (mem_roundedUpIndices_iff (m ^ 2) k).mp hk
      apply
        (mem_roundedUpIndices_iff ((m + 1) ^ 2) k).mpr
      constructor
      · have hsquare :
            (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by
          ring
        rw [hsquare]
        omega
      · exact hk'.2
    · rcases hk with ⟨t, ht, rfl⟩
      have ht' :
          t < 2 * m + 1 ∧ m + 1 ≤ t :=
        (mem_roundedUpOffsets_iff m t).mp ht
      have ht_le : t ≤ 2 * m := by
        omega
      have hup_t :
          roundsUp (m ^ 2 + t) :=
        (roundsUp_square_add_iff m t ht_le).mpr ht'.2
      apply
        (mem_roundedUpIndices_iff
          ((m + 1) ^ 2)
          (m ^ 2 + t - 1)).mpr
      constructor
      · have hsquare :
            (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by
          ring
        rw [hsquare]
        omega
      · have harg :
            m ^ 2 + t - 1 + 1 = m ^ 2 + t := by
          omega
        rw [harg]
        exact hup_t

theorem roundedUpIndices_square_succ_card
    (m : Nat) :
    (roundedUpIndices ((m + 1) ^ 2)).card =
      (roundedUpIndices (m ^ 2)).card + m := by
  rw [roundedUpIndices_square_succ_split]
  have hdisjoint :
      Disjoint
        (roundedUpIndices (m ^ 2))
        (Finset.image
          (fun t => m ^ 2 + t - 1)
          (roundedUpOffsets m)) := by
    rw [Finset.disjoint_left]
    intro k hkOld hkNew
    have hklt : k < m ^ 2 :=
      (mem_roundedUpIndices_iff (m ^ 2) k).mp hkOld |>.1
    rcases Finset.mem_image.mp hkNew with ⟨t, ht, rfl⟩
    have htLower : m + 1 ≤ t :=
      (mem_roundedUpOffsets_iff m t).mp ht |>.2
    omega
  rw [Finset.card_union_of_disjoint hdisjoint]
  have himage :
      (Finset.image
          (fun t => m ^ 2 + t - 1)
          (roundedUpOffsets m)).card =
        (roundedUpOffsets m).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have haLower : m + 1 ≤ a :=
      (mem_roundedUpOffsets_iff m a).mp ha |>.2
    have hbLower : m + 1 ≤ b :=
      (mem_roundedUpOffsets_iff m b).mp hb |>.2
    have haPos : 1 ≤ m ^ 2 + a := by
      omega
    have hbPos : 1 ≤ m ^ 2 + b := by
      omega
    have habSucc :
        (m ^ 2 + a - 1) + 1 =
          (m ^ 2 + b - 1) + 1 := by
      exact congrArg (fun x : Nat => x + 1) hab
    have habAdd :
        m ^ 2 + a = m ^ 2 + b := by
      calc
        m ^ 2 + a =
            (m ^ 2 + a - 1) + 1 := by
              exact (Nat.sub_add_cancel haPos).symm
        _ = (m ^ 2 + b - 1) + 1 := habSucc
        _ = m ^ 2 + b := by
              exact Nat.sub_add_cancel hbPos
    exact Nat.add_left_cancel habAdd
  rw [himage]
  rw [roundedUpOffsets_card]

theorem roundedUpIndices_square_card_eq_sum_range (m : Nat) :
    (roundedUpIndices (m ^ 2)).card =
      Finset.sum (Finset.range m) (fun k => k) := by
  induction m with
  | zero =>
      simp [roundedUpIndices]
  | succ m ih =>
      rw [roundedUpIndices_square_succ_card]
      rw [ih]
      rw [Finset.sum_range_succ]

theorem roundedUpIndices_square_card (m : Nat) :
    (roundedUpIndices (m ^ 2)).card =
      m * (m - 1) / 2 := by
  rw [roundedUpIndices_square_card_eq_sum_range]
  exact Finset.sum_range_id m

/--
Offsets in the partial block from `m^2` through `m^2 + r`
whose square roots are rounded upward.-/
def roundedUpOffsetsUpTo (m r : Nat) : Finset Nat :=
  (Finset.range (r + 1)).filter
    (fun t => roundsUp (m ^ 2 + t))

theorem mem_roundedUpOffsetsUpTo_iff
    (m r t : Nat)
    (hr : r ≤ 2 * m) :
    t ∈ roundedUpOffsetsUpTo m r ↔
      t ≤ r ∧ m + 1 ≤ t := by
  unfold roundedUpOffsetsUpTo
  rw [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨htRange, htRounds⟩
    have htLeR : t ≤ r := by
      exact Nat.lt_succ_iff.mp
        (by simpa [Nat.succ_eq_add_one] using
          Finset.mem_range.mp htRange)
    have htLe : t ≤ 2 * m := by
      omega
    constructor
    · exact htLeR
    · exact
        (roundsUp_square_add_iff m t htLe).mp htRounds
  · intro h
    rcases h with ⟨htLeR, htLower⟩
    have htLe : t ≤ 2 * m := by
      omega
    constructor
    · apply Finset.mem_range.mpr
      omega
    · exact
        (roundsUp_square_add_iff m t htLe).mpr htLower

theorem roundedUpOffsetsUpTo_card
    (m r : Nat)
    (hr : r ≤ 2 * m) :
    (roundedUpOffsetsUpTo m r).card = r - m := by
  have hset :
      roundedUpOffsetsUpTo m r =
        Finset.Icc (m + 1) r := by
    ext t
    rw [mem_roundedUpOffsetsUpTo_iff m r t hr]
    simp only [Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  rw [hset]
  simp

theorem roundedUpIndices_square_add_split
    (m r : Nat)
    (hr : r ≤ 2 * m) :
    roundedUpIndices (m ^ 2 + r) =
      roundedUpIndices (m ^ 2) ∪
        Finset.image
          (fun t => m ^ 2 + t - 1)
          (roundedUpOffsetsUpTo m r) := by
  ext k
  constructor
  · intro hk
    have hk' :
        k < m ^ 2 + r ∧ roundsUp (k + 1) :=
      (mem_roundedUpIndices_iff (m ^ 2 + r) k).mp hk
    rcases hk' with ⟨hklt, hup⟩
    by_cases hsmall : k < m ^ 2
    · apply Finset.mem_union_left
      exact
        (mem_roundedUpIndices_iff (m ^ 2) k).mpr
          ⟨hsmall, hup⟩
    · apply Finset.mem_union_right
      let t : Nat := k + 1 - m ^ 2
      have hmle : m ^ 2 ≤ k := by
        exact Nat.le_of_not_gt hsmall
      have ht_eq :
          m ^ 2 + t = k + 1 := by
        dsimp [t]
        omega
      have hk1le :
          k + 1 ≤ m ^ 2 + r := by
        omega
      have ht_le_r : t ≤ r := by
        dsimp [t]
        omega
      have ht_le : t ≤ 2 * m := by
        omega
      have hup_t :
          roundsUp (m ^ 2 + t) := by
        rw [ht_eq]
        exact hup
      have ht_lower : m + 1 ≤ t :=
        (roundsUp_square_add_iff m t ht_le).mp hup_t
      have ht_mem :
          t ∈ roundedUpOffsetsUpTo m r := by
        apply
          (mem_roundedUpOffsetsUpTo_iff m r t hr).mpr
        exact ⟨ht_le_r, ht_lower⟩
      apply Finset.mem_image.mpr
      refine ⟨t, ht_mem, ?_⟩
      dsimp [t]
      omega
  · intro hk
    rcases Finset.mem_union.mp hk with hkOld | hkNew
    · have hk' :
          k < m ^ 2 ∧ roundsUp (k + 1) :=
        (mem_roundedUpIndices_iff (m ^ 2) k).mp hkOld
      apply
        (mem_roundedUpIndices_iff (m ^ 2 + r) k).mpr
      constructor
      · omega
      · exact hk'.2
    · rcases Finset.mem_image.mp hkNew with ⟨t, ht, rfl⟩
      have ht' :
          t ≤ r ∧ m + 1 ≤ t :=
        (mem_roundedUpOffsetsUpTo_iff m r t hr).mp ht
      have ht_le : t ≤ 2 * m := by
        omega
      have hup_t :
          roundsUp (m ^ 2 + t) :=
        (roundsUp_square_add_iff m t ht_le).mpr ht'.2
      apply
        (mem_roundedUpIndices_iff
          (m ^ 2 + r)
          (m ^ 2 + t - 1)).mpr
      constructor
      · omega
      · have harg :
            m ^ 2 + t - 1 + 1 = m ^ 2 + t := by
          omega
        rw [harg]
        exact hup_t

/--
The nearest-root sum is the floor-root sum plus the number
of terms rounded upward.-/
theorem nearestRootSum_eq_rootSum_add_bonus (n : Nat) :
    nearestRootSum n =
      rootSum n +
        Finset.sum (Finset.range n)
          (fun k => nearestBonus (k + 1)) := by
  unfold nearestRootSum rootSum
  simp_rw [nearestSqrt_eq_sqrt_add_bonus]
  rw [Finset.sum_add_distrib]

theorem nearestRootSum_eq_rootSum_add_bonusSum (n : Nat) :
    nearestRootSum n = rootSum n + nearestBonusSum n := by
  rw [nearestRootSum_eq_rootSum_add_bonus]
  rfl

theorem nearestBonusSum_eq_card_roundedUpIndices (n : Nat) :
    nearestBonusSum n = (roundedUpIndices n).card := by
  unfold nearestBonusSum roundedUpIndices
  simp_rw [nearestBonus_eq_indicator]
  exact
    (Finset.card_filter
      (fun k : Nat => roundsUp (k + 1))
      (Finset.range n)).symm

theorem nearestRootSum_eq_rootSum_add_card (n : Nat) :
    nearestRootSum n =
      rootSum n + (roundedUpIndices n).card := by
  rw [nearestRootSum_eq_rootSum_add_bonusSum]
  rw [nearestBonusSum_eq_card_roundedUpIndices]

theorem roundedUpIndices_square_add_card
    (m r : Nat)
    (hr : r ≤ 2 * m) :
    (roundedUpIndices (m ^ 2 + r)).card =
      (roundedUpIndices (m ^ 2)).card + (r - m) := by
  rw [roundedUpIndices_square_add_split m r hr]
  have hdisjoint :
      Disjoint
        (roundedUpIndices (m ^ 2))
        (Finset.image
          (fun t => m ^ 2 + t - 1)
          (roundedUpOffsetsUpTo m r)) := by
    rw [Finset.disjoint_left]
    intro k hkOld hkNew
    have hklt : k < m ^ 2 :=
      (mem_roundedUpIndices_iff (m ^ 2) k).mp hkOld |>.1
    rcases Finset.mem_image.mp hkNew with ⟨t, ht, rfl⟩
    have htLower : m + 1 ≤ t :=
      (mem_roundedUpOffsetsUpTo_iff m r t hr).mp ht |>.2
    omega
  rw [Finset.card_union_of_disjoint hdisjoint]
  have himage :
      (Finset.image
          (fun t => m ^ 2 + t - 1)
          (roundedUpOffsetsUpTo m r)).card =
        (roundedUpOffsetsUpTo m r).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have haLower : m + 1 ≤ a :=
      (mem_roundedUpOffsetsUpTo_iff m r a hr).mp ha |>.2
    have hbLower : m + 1 ≤ b :=
      (mem_roundedUpOffsetsUpTo_iff m r b hr).mp hb |>.2
    have haPos : 1 ≤ m ^ 2 + a := by
      omega
    have hbPos : 1 ≤ m ^ 2 + b := by
      omega
    have habSucc :
        (m ^ 2 + a - 1) + 1 =
          (m ^ 2 + b - 1) + 1 := by
      exact congrArg (fun x : Nat => x + 1) hab
    have habAdd :
        m ^ 2 + a = m ^ 2 + b := by
      calc
        m ^ 2 + a =
            (m ^ 2 + a - 1) + 1 := by
              exact (Nat.sub_add_cancel haPos).symm
        _ = (m ^ 2 + b - 1) + 1 := habSucc
        _ = m ^ 2 + b := by
              exact Nat.sub_add_cancel hbPos
    exact Nat.add_left_cancel habAdd
  rw [himage]
  rw [roundedUpOffsetsUpTo_card m r hr]

theorem roundedUpIndices_square_add_card_explicit
    (m r : Nat)
    (hr : r ≤ 2 * m) :
    (roundedUpIndices (m ^ 2 + r)).card =
      m * (m - 1) / 2 + (r - m) := by
  rw [roundedUpIndices_square_add_card m r hr]
  rw [roundedUpIndices_square_card]

theorem nearestBonusSum_formula (n : Nat) :
    nearestBonusSum n =
      Nat.sqrt n * (Nat.sqrt n - 1) / 2 +
        (n - Nat.sqrt n ^ 2 - Nat.sqrt n) := by
  let m : Nat := Nat.sqrt n
  let r : Nat := n - m ^ 2
  have hm_sq_le : m ^ 2 ≤ n := by
    apply (Nat.le_sqrt').mp
    simp [m]
  have hn_lt : n < (m + 1) ^ 2 := by
    exact
      ((Nat.eq_sqrt').mp
        (by rfl : m = Nat.sqrt n)).2
  have hsquare :
      (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by
    ring
  have hr : r ≤ 2 * m := by
    dsimp [r]
    rw [hsquare] at hn_lt
    omega
  have hn_decomp :
      m ^ 2 + r = n := by
    dsimp [r]
    omega
  calc
    nearestBonusSum n =
        (roundedUpIndices n).card :=
      nearestBonusSum_eq_card_roundedUpIndices n
    _ = (roundedUpIndices (m ^ 2 + r)).card := by
      rw [hn_decomp]
    _ = m * (m - 1) / 2 + (r - m) :=
      roundedUpIndices_square_add_card_explicit m r hr
    _ =
        Nat.sqrt n * (Nat.sqrt n - 1) / 2 +
          (n - Nat.sqrt n ^ 2 - Nat.sqrt n) := by
      rfl

theorem nearestRootSum_formula (n : Nat) :
    nearestRootSum n =
      rootSum n +
        Nat.sqrt n * (Nat.sqrt n - 1) / 2 +
        (n - Nat.sqrt n ^ 2 - Nat.sqrt n) := by
  rw [nearestRootSum_eq_rootSum_add_bonusSum]
  rw [nearestBonusSum_formula]
  simp [Nat.add_assoc]

theorem nearestRootSum_explicit_formula (n : Nat) :
    nearestRootSum n =
      Nat.sqrt n * (n + 1) -
        Nat.sqrt n * (Nat.sqrt n + 1) *
          (2 * Nat.sqrt n + 1) / 6 +
        Nat.sqrt n * (Nat.sqrt n - 1) / 2 +
        (n - Nat.sqrt n ^ 2 - Nat.sqrt n) := by
  rw [nearestRootSum_formula]
  rw [rootSum_explicit_formula]
  simp [rootIndex]

end RoundedRootSums
