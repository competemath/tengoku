/-
Copyright (c) 2026 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Marios Georgiou
-/

import Tengoku.RobustInverseUncertaintyLean.LeanFormalization.Basic
import Tengoku.Seed.Algebra.Module.ZMod
import Tengoku.Seed.Data.Finset.SymmDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative combinatorics for robust inverse uncertainty

This file develops the real Walsh counting identities used in the robust
almost-orthogonality argument.
-/

namespace RobustInverseUncertainty

noncomputable section

open scoped BigOperators Finset Pointwise symmDiff
attribute [local instance] Classical.propDecidable

/-- The real Walsh sign associated to the standard Boolean pairing.-/
def realPhase {n : ℕ} (x y : BooleanSpace n) : ℝ :=
  if dot x y = 0 then 1 else -1

/--
@isnad1 id=eq.0h2v.s6.fdd2dfa92a76 from=translated src=- shape=38f5e75a vocab=edb26409
-/
@[simp]
theorem realPhase_zero_left {n : ℕ} (y : BooleanSpace n) :
    realPhase 0 y = 1 := by
  simp [realPhase]

/--
@isnad1 id=eq.0h2v.s6.400b80fbd2a5 from=translated src=- shape=60a0e6ad vocab=edb26409
-/
@[simp]
theorem realPhase_zero_right {n : ℕ} (x : BooleanSpace n) :
    realPhase x 0 = 1 := by
  simp [realPhase]

/--
@isnad1 id=iff.0h3v.s6.fe3fb72708a8 from=translated src=- shape=991ed5e0 vocab=f9259149
-/
@[simp]
theorem realPhase_eq_one_iff {n : ℕ} {x y : BooleanSpace n} :
    realPhase x y = 1 ↔ dot x y = 0 := by
  simp only [realPhase]
  split_ifs with h
  · simp [h]
  · norm_num [h]

/--
@isnad1 id=iff.0h3v.s6.d4d66e0d48bc from=translated src=- shape=53105387 vocab=a3db3d46
-/
@[simp]
theorem realPhase_eq_neg_one_iff {n : ℕ} {x y : BooleanSpace n} :
    realPhase x y = -1 ↔ dot x y = 1 := by
  rcases zmod_two_eq_zero_or_one (dot x y) with h | h
  · simp [realPhase, h, show (1 : ℝ) ≠ -1 by norm_num]
  · simp [realPhase, h]

/--
@isnad1 id=eq.0h3v.s5.df73a3f26a03 from=translated src=- shape=f8527af6 vocab=4f39510d
-/
@[simp]
theorem realPhase_sq {n : ℕ} (x y : BooleanSpace n) :
    realPhase x y ^ 2 = 1 := by
  simp only [realPhase]
  split_ifs <;> norm_num

/--
@isnad1 id=eq.0h3v.s4.d281c8c12896 from=translated src=- shape=0008002d vocab=794ff6cf
-/
@[simp]
theorem ofReal_realPhase {n : ℕ} (x y : BooleanSpace n) :
    (realPhase x y : ℂ) = phase x y := by
  simp only [realPhase, phase, bitPhase]
  split_ifs <;> norm_num

/--
@isnad1 id=eq.0h4v.s6.5cef91c6c6fa from=translated src=- shape=6a42c977 vocab=38307e50
-/
@[simp]
theorem realPhase_add_left {n : ℕ} (x y z : BooleanSpace n) :
    realPhase (x + y) z = realPhase x z * realPhase y z := by
  apply Complex.ofReal_injective
  calc
    (realPhase (x + y) z : ℂ) = phase (x + y) z :=
      ofReal_realPhase (x + y) z
    _ = phase x z * phase y z := phase_add_left x y z
    _ = (realPhase x z * realPhase y z : ℝ) := by
      rw [Complex.ofReal_mul, ofReal_realPhase, ofReal_realPhase]

/--
@isnad1 id=eq.0h4v.s6.20ed00f5c7f8 from=translated src=- shape=dbcefff3 vocab=38307e50
-/
@[simp]
theorem realPhase_add_right {n : ℕ} (x y z : BooleanSpace n) :
    realPhase x (y + z) = realPhase x y * realPhase x z := by
  apply Complex.ofReal_injective
  calc
    (realPhase x (y + z) : ℂ) = phase x (y + z) :=
      ofReal_realPhase x (y + z)
    _ = phase x y * phase x z := phase_add_right x y z
    _ = (realPhase x y * realPhase x z : ℝ) := by
      rw [Complex.ofReal_mul, ofReal_realPhase, ofReal_realPhase]

/--
@isnad1 id=eq.0h3v.s4.039a4449dcab from=translated src=- shape=7a5478ec vocab=5422cfa5
-/
theorem realPhase_comm {n : ℕ} (x y : BooleanSpace n) :
    realPhase x y = realPhase y x := by
  simp [realPhase, dot_comm]

/-- The real Walsh sign as a bundled additive character.-/
def realPhaseChar {n : ℕ} (y : BooleanSpace n) :
    AddChar (BooleanSpace n) ℝ where
  toFun x := realPhase x y
  map_zero_eq_one' := realPhase_zero_left y
  map_add_eq_mul' := fun x z ↦ realPhase_add_left x z y

/--
@isnad1 id=eq.0h3v.s7.b3b5a85ff604 from=translated src=- shape=13981332 vocab=aa2ed4bc
-/
@[simp]
theorem realPhaseChar_apply {n : ℕ} (x y : BooleanSpace n) :
    realPhaseChar y x = realPhase x y := rfl

/--
@isnad1 id=iff.0h2v.s8.cff06b0422cf from=translated src=- shape=36d4868c vocab=5cf0a5df
-/
@[simp]
theorem realPhaseChar_eq_zero_iff {n : ℕ} (y : BooleanSpace n) :
    realPhaseChar y = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext i
    have hi := DFunLike.congr_fun h (Pi.single i (1 : ZMod 2))
    change realPhase (Pi.single i 1) y = 1 at hi
    simpa using (realPhase_eq_one_iff.mp hi)
  · rintro rfl
    ext x
    simp [realPhaseChar]

/-- Orthogonality of the real Walsh characters on the Boolean cube.
@isnad1 id=eq.0h2v.s7.d2087eed9cef from=translated src=- shape=cc7c232c vocab=4e26b2e9
-/
theorem sum_realPhase_eq_ite {n : ℕ} (y : BooleanSpace n) :
    ∑ x : BooleanSpace n, realPhase x y =
      if y = 0 then (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
  simpa using AddChar.sum_eq_ite (realPhaseChar y)

/-- The unnormalized real Walsh sum of a finite set.-/
def realWalshSum {n : ℕ} (A : Finset (BooleanSpace n))
    (y : BooleanSpace n) : ℝ :=
  ∑ x ∈ A, realPhase x y

/--
@isnad1 id=eq.0h3v.s7.d83f96217ee3 from=translated src=- shape=c8f06c9c vocab=57c2f9c8
-/
theorem realWalshSum_eq_card_sub_two_bad {n : ℕ}
    (A : Finset (BooleanSpace n)) (y : BooleanSpace n) :
    realWalshSum A y =
      (A.card : ℝ) -
        2 * ((A.filter fun x ↦ dot x y = 1).card : ℝ) := by
  classical
  rw [realWalshSum]
  calc
    (∑ x ∈ A, realPhase x y) =
        ∑ x ∈ A, (1 - 2 * if dot x y = 1 then 1 else 0 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases zmod_two_eq_zero_or_one (dot x y) with h | h
      · simp [realPhase, h]
      · simp [realPhase, h]
        norm_num
    _ = (A.card : ℝ) -
        2 * ((A.filter fun x ↦ dot x y = 1).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [← Finset.mul_sum]
      simp

/--
@isnad1 id=eq.0h3v.s7.0c236200a7cf from=translated src=- shape=f1c8f5b0 vocab=dd403120
-/
theorem sum_realPhase_mul_realPhase {n : ℕ}
    (x z : BooleanSpace n) :
    ∑ y : BooleanSpace n, realPhase x y * realPhase z y =
      if x = z then (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
  calc
    (∑ y : BooleanSpace n, realPhase x y * realPhase z y) =
        ∑ y : BooleanSpace n, realPhase y (x + z) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [realPhase_comm x y, realPhase_comm z y,
        ← realPhase_add_right]
    _ = if x + z = 0 then
          (Fintype.card (BooleanSpace n) : ℝ) else 0 :=
      sum_realPhase_eq_ite (x + z)
    _ = if x = z then
          (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
      by_cases h : x = z
      · simp [h]
      · simp [h, add_eq_zero_iff_eq_neg, neg_eq_self]

/-- Parseval for an indicator, in unnormalized real Walsh coordinates.
@isnad1 id=eq.0h2v.s6.d3e3d2541dbd from=translated src=- shape=36c1515b vocab=4d70afaa
-/
theorem realWalshSum_parseval {n : ℕ}
    (A : Finset (BooleanSpace n)) :
    ∑ y : BooleanSpace n, realWalshSum A y ^ 2 =
      (Fintype.card (BooleanSpace n) : ℝ) * A.card := by
  classical
  calc
    (∑ y : BooleanSpace n, realWalshSum A y ^ 2) =
        ∑ y : BooleanSpace n, ∑ x ∈ A, ∑ z ∈ A,
          realPhase x y * realPhase z y := by
      simp only [realWalshSum, pow_two, Finset.sum_mul_sum]
    _ = ∑ x ∈ A, ∑ z ∈ A, ∑ y : BooleanSpace n,
          realPhase x y * realPhase z y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ A, ∑ z ∈ A,
          if x = z then (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
      simp_rw [sum_realPhase_mul_realPhase]
    _ = (Fintype.card (BooleanSpace n) : ℝ) * A.card := by
      simp
      ring

/-- Number of elements of `A` that pair nontrivially with `y`.-/
def badCount {n : ℕ} (A : Finset (BooleanSpace n))
    (y : BooleanSpace n) : ℕ :=
  (A.filter fun x ↦ dot x y = 1).card

/-- Number of nonorthogonal pairs in `A × B`.-/
def badPairCount {n : ℕ} (A B : Finset (BooleanSpace n)) : ℕ :=
  ∑ y ∈ B, badCount A y

/--
@isnad1 id=eq.0h2v.s6.6b12a9275900 from=translated src=- shape=56f57d2f vocab=71beb6ef
-/
@[simp]
theorem badCount_zero {n : ℕ} (A : Finset (BooleanSpace n)) :
    badCount A 0 = 0 := by
  simp [badCount]

/--
@isnad1 id=le.0h3v.s4.60821b995dc7 from=translated src=- shape=9f3a6a53 vocab=cdb33ed7
-/
theorem badCount_le_card {n : ℕ} (A : Finset (BooleanSpace n))
    (y : BooleanSpace n) :
    badCount A y ≤ A.card := by
  exact Finset.card_filter_le _ _

/--
@isnad1 id=le.0h4v.s6.1b8b0bf0f103 from=translated src=- shape=345ce289 vocab=8b8177d6
-/
theorem badCount_add_le {n : ℕ} (A : Finset (BooleanSpace n))
    (y z : BooleanSpace n) :
    badCount A (y + z) ≤ badCount A y + badCount A z := by
  classical
  let Ay := A.filter fun x ↦ dot x y = 1
  let Az := A.filter fun x ↦ dot x z = 1
  have hsub :
      A.filter (fun x ↦ dot x (y + z) = 1) ⊆ Ay ∪ Az := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_union, Finset.mem_filter, Ay, Az, hx.1, true_and]
    rw [dot_add_right] at hx
    rcases zmod_two_eq_zero_or_one (dot x y) with hy | hy <;>
      rcases zmod_two_eq_zero_or_one (dot x z) with hz | hz
    · simp [hy, hz] at hx
    · exact Or.inr hz
    · exact Or.inl hy
    · simp [hy, hz] at hx
  calc
    badCount A (y + z) ≤ (Ay ∪ Az).card :=
      Finset.card_le_card hsub
    _ ≤ Ay.card + Az.card := Finset.card_union_le _ _
    _ = badCount A y + badCount A z := rfl

/-- Elements of `B` whose bad count against `A` is at most `q |A|`.-/
def lowBiasSet {n : ℕ} (A B : Finset (BooleanSpace n)) (q : ℝ) :
    Finset (BooleanSpace n) :=
  B.filter fun y ↦ (badCount A y : ℝ) ≤ q * A.card

/--
@isnad1 id=le.0h4v.s5.e4267384486f from=translated src=- shape=77100776 vocab=b9b04091
-/
theorem lowBiasSet_subset_right {n : ℕ}
    (A B : Finset (BooleanSpace n)) (q : ℝ) :
    lowBiasSet A B q ⊆ B :=
  Finset.filter_subset _ _

/--
@isnad1 id=mem.2h4v.s7.f66896a7ba27 from=translated src=- shape=019d7127 vocab=63b938cc
-/
theorem zero_mem_lowBiasSet {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hzero : 0 ∈ B) (hq : 0 ≤ q) :
    0 ∈ lowBiasSet A B q := by
  simp [lowBiasSet, hzero]
  positivity

/--
@isnad1 id=eq.0h3v.s5.7769950ee390 from=translated src=- shape=fd016b84 vocab=8ee77b90
-/
theorem badPairCount_eq_sum {n : ℕ}
    (A B : Finset (BooleanSpace n)) :
    (badPairCount A B : ℝ) =
      ∑ y ∈ B, (badCount A y : ℝ) := by
  simp [badPairCount]

/--
Finite Markov inequality for bad counts.  The denominator-free hypothesis is
`badPairCount A B ≤ q² |A| |B|`.
@isnad1 id=le.2h4v.s7.d32d55c3e2f9 from=translated src=- shape=db02de98 vocab=29fd12e3
-/
theorem card_sdiff_lowBiasSet_le {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq : 0 ≤ q)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    ((B \ lowBiasSet A B q).card : ℝ) * q * A.card ≤
      q ^ 2 * A.card * B.card := by
  classical
  have heach : ∀ y ∈ B \ lowBiasSet A B q,
      q * (A.card : ℝ) ≤ badCount A y := by
    intro y hy
    simp only [Finset.mem_sdiff, lowBiasSet, Finset.mem_filter,
      not_and, not_le] at hy
    exact (hy.2 hy.1).le
  calc
    ((B \ lowBiasSet A B q).card : ℝ) * q * A.card =
        ∑ y ∈ B \ lowBiasSet A B q, q * (A.card : ℝ) := by
      simp [mul_assoc]
    _ ≤ ∑ y ∈ B \ lowBiasSet A B q, (badCount A y : ℝ) :=
      Finset.sum_le_sum fun y hy ↦ heach y hy
    _ ≤ ∑ y ∈ B, (badCount A y : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro y hyB hyDiff
      positivity
    _ = (badPairCount A B : ℝ) := (badPairCount_eq_sum A B).symm
    _ ≤ q ^ 2 * A.card * B.card := hbad

/--
@isnad1 id=le.3h4v.s6.a57ff27bba96 from=translated src=- shape=fc06400a vocab=72b28957
-/
theorem card_lowBiasSet_lower {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq : 0 < q) (hA : A.Nonempty)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    (1 - q) * B.card ≤ (lowBiasSet A B q).card := by
  have hmarkov := card_sdiff_lowBiasSet_le A B hq.le hbad
  have hApos : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hqA : 0 < q * (A.card : ℝ) := mul_pos hq hApos
  have hdiff :
      ((B \ lowBiasSet A B q).card : ℝ) ≤ q * B.card := by
    nlinarith [hmarkov]
  have hpartition :
      ((B \ lowBiasSet A B q).card : ℝ) +
          (lowBiasSet A B q).card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card
      (lowBiasSet_subset_right A B q)
  nlinarith

/-- Frequencies whose bad count against `A` is at most `2q |A|`.-/
def highBiasSet {n : ℕ} (A : Finset (BooleanSpace n)) (q : ℝ) :
    Finset (BooleanSpace n) :=
  Finset.univ.filter fun y ↦
    (badCount A y : ℝ) ≤ 2 * q * A.card

/--
@isnad1 id=le.0h4v.s7.fc19591ed418 from=translated src=- shape=a3458a10 vocab=97023014
-/
theorem lowBiasSet_add_self_subset_highBiasSet {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ} :
    lowBiasSet A B q + lowBiasSet A B q ⊆ highBiasSet A q := by
  classical
  intro w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp hw
  simp only [lowBiasSet, Finset.mem_filter] at hy hz
  simp only [highBiasSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hadd := badCount_add_le A y z
  have haddR :
      (badCount A (y + z) : ℝ) ≤
        badCount A y + badCount A z := by
    exact_mod_cast hadd
  nlinarith

/-- Parseval bounds the number of frequencies with very high Walsh bias.
@isnad1 id=le.2h3v.s7.1e2bd80b6c99 from=translated src=- shape=31d6328b vocab=4cfe20c5
-/
theorem highBiasSet_card_bound {n : ℕ}
    (A : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq4 : 4 * q ≤ 1) :
    ((highBiasSet A q).card : ℝ) *
        (((1 - 4 * q) * A.card) ^ 2) ≤
      Fintype.card (BooleanSpace n) * A.card := by
  classical
  let c : ℝ := (1 - 4 * q) * A.card
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hpoint : ∀ y ∈ highBiasSet A q,
      c ^ 2 ≤ realWalshSum A y ^ 2 := by
    intro y hy
    have hybad :
        (badCount A y : ℝ) ≤ 2 * q * A.card := by
      simpa [highBiasSet] using hy
    have hwalsh :
        c ≤ realWalshSum A y := by
      rw [realWalshSum_eq_card_sub_two_bad]
      dsimp [badCount] at hybad ⊢
      dsimp [c]
      nlinarith
    exact (sq_le_sq₀ hc (hc.trans hwalsh)).2 hwalsh
  calc
    ((highBiasSet A q).card : ℝ) * (((1 - 4 * q) * A.card) ^ 2) =
        ∑ y ∈ highBiasSet A q, c ^ 2 := by
      simp [c]
    _ ≤ ∑ y ∈ highBiasSet A q, realWalshSum A y ^ 2 :=
      Finset.sum_le_sum fun y hy ↦ hpoint y hy
    _ ≤ ∑ y : BooleanSpace n, realWalshSum A y ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (show highBiasSet A q ⊆ Finset.univ from Finset.subset_univ _)
      intro y hy hnot
      positivity
    _ = Fintype.card (BooleanSpace n) * A.card :=
      realWalshSum_parseval A

/--
@isnad1 id=le.2h4v.s8.e66526a11b7a from=translated src=- shape=0c04a98a vocab=0e166e98
-/
theorem lowBiasSet_sum_card_bound {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq4 : 4 * q ≤ 1) :
    (((lowBiasSet A B q + lowBiasSet A B q).card : ℝ) *
        (((1 - 4 * q) * A.card) ^ 2)) ≤
      (Fintype.card (BooleanSpace n) : ℝ) * (A.card : ℝ) := by
  have hcard : (lowBiasSet A B q + lowBiasSet A B q).card ≤
      (highBiasSet A q).card :=
    Finset.card_le_card (lowBiasSet_add_self_subset_highBiasSet A B)
  have hnonneg : 0 ≤ (((1 - 4 * q) * (A.card : ℝ)) ^ 2) := sq_nonneg _
  calc
    (((lowBiasSet A B q + lowBiasSet A B q).card : ℝ) *
        (((1 - 4 * q) * A.card) ^ 2)) ≤
        ((highBiasSet A q).card : ℝ) *
          (((1 - 4 * q) * A.card) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnonneg
    _ ≤ (Fintype.card (BooleanSpace n) : ℝ) * (A.card : ℝ) :=
      highBiasSet_card_bound A hq0 hq4

/-- The elementary numerical estimate behind the `< 3/2` threshold.
@isnad1 id=lt.7h6v.s7.dc7bf38fd6c1 from=translated src=- shape=2260fee3 vocab=e7bc5859
-/
theorem numerical_doubling_bound
    {q a b N x y : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100)
    (ha : 0 < a) (hy : 0 < y)
    (hN : (1 - q) * N ≤ a * b)
    (hx : (1 - q) * b ≤ x)
    (hparseval : y * (((1 - 4 * q) * a) ^ 2) ≤ N * a) :
    y < (3 / 2 : ℝ) * x := by
  have hq1 : 0 < 1 - q := by linarith
  have hcancelA :
      y * (1 - 4 * q) ^ 2 * a ≤ N := by
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      (y * (1 - 4 * q) ^ 2 * a) * a =
          y * (((1 - 4 * q) * a) ^ 2) := by ring
      _ ≤ N * a := hparseval
  have htoB :
      (1 - q) * (y * (1 - 4 * q) ^ 2) ≤ b := by
    apply (mul_le_mul_iff_right₀ ha).mp
    calc
      a * ((1 - q) * (y * (1 - 4 * q) ^ 2)) =
          (1 - q) * (y * (1 - 4 * q) ^ 2 * a) := by ring
      _ ≤ (1 - q) * N :=
        mul_le_mul_of_nonneg_left hcancelA hq1.le
      _ ≤ a * b := hN
  have hdenom :
      (1 - q) ^ 2 * (1 - 4 * q) ^ 2 * y ≤ x := by
    calc
      (1 - q) ^ 2 * (1 - 4 * q) ^ 2 * y =
          (1 - q) * ((1 - q) * (y * (1 - 4 * q) ^ 2)) := by ring
      _ ≤ (1 - q) * b :=
        mul_le_mul_of_nonneg_left htoB hq1.le
      _ ≤ x := hx
  have h19a : (19 / 20 : ℝ) ≤ 1 - q := by linarith
  have h19b : (19 / 20 : ℝ) ≤ 1 - 4 * q := by linarith
  have hsqa : (19 / 20 : ℝ) ^ 2 ≤ (1 - q) ^ 2 := by
    exact (sq_le_sq₀ (by norm_num) (by linarith)).2 h19a
  have hsqb : (19 / 20 : ℝ) ^ 2 ≤ (1 - 4 * q) ^ 2 := by
    exact (sq_le_sq₀ (by norm_num) (by linarith)).2 h19b
  have hprod :
      (19 / 20 : ℝ) ^ 4 ≤
        (1 - q) ^ 2 * (1 - 4 * q) ^ 2 := by
    calc
      (19 / 20 : ℝ) ^ 4 =
          (19 / 20 : ℝ) ^ 2 * (19 / 20 : ℝ) ^ 2 := by ring
      _ ≤ (1 - q) ^ 2 * (1 - 4 * q) ^ 2 :=
        mul_le_mul hsqa hsqb (sq_nonneg _) (sq_nonneg _)
  have htwoThirds :
      (2 / 3 : ℝ) <
        (1 - q) ^ 2 * (1 - 4 * q) ^ 2 := by
    have : (2 / 3 : ℝ) < (19 / 20 : ℝ) ^ 4 := by norm_num
    linarith
  have hstrict :
      (2 / 3 : ℝ) * y <
        ((1 - q) ^ 2 * (1 - 4 * q) ^ 2) * y :=
    mul_lt_mul_of_pos_right htwoThirds hy
  nlinarith

/--
For saturated almost-orthogonal sets, the low-bias subset has doubling
strictly below `3/2`.
@isnad1 id=lt.6h4v.s8.c5912a92a06a from=translated src=- shape=c6247892 vocab=978c6fca
-/
theorem lowBiasSet_doubling_lt_three_halves {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hA : A.Nonempty) (hzero : 0 ∈ B)
    (hsat :
      (1 - q) * Fintype.card (BooleanSpace n) ≤
        (A.card : ℝ) * B.card)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    ((lowBiasSet A B q + lowBiasSet A B q).card : ℚ) <
      (3 / 2 : ℚ) * (lowBiasSet A B q).card := by
  let X := lowBiasSet A B q
  have hXzero : 0 ∈ X := zero_mem_lowBiasSet A B hzero hq0.le
  have hX : X.Nonempty := ⟨0, hXzero⟩
  have hXX : (X + X).Nonempty := by
    exact ⟨0, Finset.mem_add.mpr ⟨0, hXzero, 0, hXzero, by simp⟩⟩
  have hq4 : 4 * q ≤ 1 := by linarith
  have hx := card_lowBiasSet_lower A B hq0 hA hbad
  have hp := lowBiasSet_sum_card_bound A B hq0.le hq4
  have hreal :
      ((X + X).card : ℝ) < (3 / 2 : ℝ) * X.card := by
    apply numerical_doubling_bound
      (q := q) (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (N := (Fintype.card (BooleanSpace n) : ℝ))
      (x := (X.card : ℝ)) (y := ((X + X).card : ℝ))
      hq0.le hq
    · exact_mod_cast hA.card_pos
    · exact_mod_cast hXX.card_pos
    · simpa [X] using hsat
    · simpa [X] using hx
    · simpa [X] using hp
  have hrat :
      (((X + X).card : ℚ) < (3 / 2 : ℚ) * X.card) := by
    have hreal' :
        (2 : ℝ) * (X + X).card < 3 * X.card := by
      nlinarith
    have hnat : 2 * (X + X).card < 3 * X.card := by
      exact_mod_cast hreal'
    have hrat' :
        (2 : ℚ) * (X + X).card < 3 * X.card := by
      exact_mod_cast hnat
    nlinarith
  simpa [X] using hrat

/--
The additive form of the sharp small-doubling theorem, specialized to the
Boolean vector space and returned as a `ZMod 2` submodule.
@isnad1 id=ex.1h2v.s10.23e283cc6a13 from=translated src=- shape=c1500e13 vocab=a20205bb
-/
theorem small_sumset_is_submodule {n : ℕ}
    (X : Finset (BooleanSpace n))
    (hX : ((X + X).card : ℚ) < (3 / 2 : ℚ) * X.card) :
    ∃ L : Submodule (ZMod 2) (BooleanSpace n),
      (L : Set (BooleanSpace n)) =
        (↑(X + X) : Set (BooleanSpace n)) := by
  classical
  let XM : Finset (Multiplicative (BooleanSpace n)) :=
    X.image Multiplicative.ofAdd
  have hprod :
      XM * XM = (X + X).image Multiplicative.ofAdd := by
    ext w
    simp only [Finset.mem_mul, Finset.mem_image, Finset.mem_add, XM]
    constructor
    · rintro ⟨wy, ⟨y, hy, rfl⟩, wz, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨y + z, ⟨y, hy, z, hz, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, z, hz, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd y, ⟨y, hy, rfl⟩,
        Multiplicative.ofAdd z, ⟨z, hz, rfl⟩, rfl⟩
  have hcardX : XM.card = X.card := by
    exact Finset.card_image_of_injective X Multiplicative.ofAdd.injective
  have hcardXX : (XM * XM).card = (X + X).card := by
    rw [hprod]
    exact Finset.card_image_of_injective (X + X)
      Multiplicative.ofAdd.injective
  have hXM :
      ((XM * XM).card : ℚ) < (3 / 2 : ℚ) * XM.card := by
    simpa [hcardX, hcardXX] using hX
  obtain ⟨H, hH⟩ := small_doubling_is_subgroup XM hXM
  let L : Submodule (ZMod 2) (BooleanSpace n) :=
    AddSubgroup.toZModSubmodule 2 H.toAddSubgroup'
  refine ⟨L, ?_⟩
  ext w
  change w ∈ AddSubgroup.toZModSubmodule 2 H.toAddSubgroup' ↔
    w ∈ X + X
  simp only [AddSubgroup.mem_toZModSubmodule, Subgroup.mem_toAddSubgroup']
  change Multiplicative.ofAdd w ∈
      (H : Set (Multiplicative (BooleanSpace n))) ↔ w ∈ X + X
  have hwH := Set.ext_iff.mp hH (Multiplicative.ofAdd w)
  rw [hwH]
  rw [← Finset.coe_mul]
  change Multiplicative.ofAdd w ∈ XM * XM ↔ w ∈ X + X
  rw [hprod]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, hzw⟩
    have hzw' : z = w := Multiplicative.ofAdd.injective hzw
    simpa [hzw'] using hz
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- The finite set of vectors in a Boolean subspace.-/
def submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n)) :
    Finset (BooleanSpace n) :=
  Finset.univ.filter fun x ↦ x ∈ L

/--
@isnad1 id=iff.0h3v.s9.a68f9cf34204 from=translated src=- shape=3269eace vocab=131fa41f
-/
@[simp]
theorem mem_submodulePoints {n : ℕ}
    {L : Submodule (ZMod 2) (BooleanSpace n)}
    {x : BooleanSpace n} :
    x ∈ submodulePoints L ↔ x ∈ L := by
  simp [submodulePoints]

/--
@isnad1 id=eq.0h2v.s11.a0242ca64540 from=translated src=- shape=78d2a682 vocab=ead9a421
-/
@[simp]
theorem card_submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n)) :
    (submodulePoints L).card = Fintype.card L := by
  rw [Fintype.card_subtype]
  rfl

/--
@isnad1 id=eq.0h2v.s7.af2fc9743a31 from=translated src=- shape=fb73a3d9 vocab=6db46670
-/
theorem submodulePoints_perp_card_mul {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n)) :
    (submodulePoints L).card * (submodulePoints (perp L)).card = 2 ^ n := by
  rw [card_submodulePoints, card_submodulePoints,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := L),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := perp L),
    ZMod.card, finrank_perp, ← pow_add]
  congr 1
  have hle : Module.finrank (ZMod 2) L ≤ n := by
    simpa using L.finrank_le
  exact Nat.add_sub_of_le hle

/-- The real Walsh character restricted to a Boolean subspace.-/
def restrictedRealPhaseChar {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) : AddChar L ℝ :=
  (realPhaseChar y).compAddMonoidHom L.subtype.toAddMonoidHom

/--
@isnad1 id=eq.0h4v.s12.44a9f7a93abf from=translated src=- shape=b3095540 vocab=a8c7dde1
-/
@[simp]
theorem restrictedRealPhaseChar_apply {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) (x : L) :
    restrictedRealPhaseChar L y x = realPhase x y := rfl

/--
@isnad1 id=iff.0h3v.s13.cb474151f1ce from=translated src=- shape=8e6f5944 vocab=af1f136f
-/
@[simp]
theorem restrictedRealPhaseChar_eq_zero_iff {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) :
    restrictedRealPhaseChar L y = 0 ↔ y ∈ perp L := by
  constructor
  · intro hzero
    rw [mem_perp_iff]
    intro x hx
    have hv := DFunLike.congr_fun hzero ⟨x, hx⟩
    change realPhase x y = 1 at hv
    exact realPhase_eq_one_iff.mp hv
  · intro hy
    rw [mem_perp_iff] at hy
    ext x
    simp [restrictedRealPhaseChar, realPhase, hy x x.property]

/--
@isnad1 id=eq.0h3v.s12.2bdc692f4e98 from=translated src=- shape=8e9288ca vocab=5cc933ff
-/
theorem sum_realPhase_submodule_eq_ite {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) :
    ∑ x : L, realPhase x y =
      if y ∈ perp L then (Fintype.card L : ℝ) else 0 := by
  simpa using AddChar.sum_eq_ite (restrictedRealPhaseChar L y)

/--
@isnad1 id=eq.0h3v.s11.90862da6554f from=translated src=- shape=fd2f6d33 vocab=ecfba68a
-/
theorem realWalshSum_submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) :
    realWalshSum (submodulePoints L) y =
      ∑ x : L, realPhase x y := by
  classical
  rw [realWalshSum]
  exact Finset.sum_subtype (p := fun x ↦ x ∈ L)
    (submodulePoints L) (by simp) (fun x ↦ realPhase x y)

/-- Outside `Lᗮ`, exactly half of `L` pairs nontrivially with `y`.
@isnad1 id=eq.1h3v.s9.7b1a105b0978 from=translated src=- shape=70e4ceb2 vocab=ca403943
-/
theorem two_mul_badCount_submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) (hy : y ∉ perp L) :
    2 * badCount (submodulePoints L) y =
      (submodulePoints L).card := by
  have hsum : realWalshSum (submodulePoints L) y = 0 := by
    rw [realWalshSum_submodulePoints, sum_realPhase_submodule_eq_ite]
    simp [hy]
  rw [realWalshSum_eq_card_sub_two_bad] at hsum
  dsimp [badCount] at hsum ⊢
  exact_mod_cast (by nlinarith : (2 : ℝ) *
    ((submodulePoints L).filter fun x ↦ dot x y = 1).card =
      (submodulePoints L).card)

/--
@isnad1 id=eq.0h3v.s4.dd5adf5d0414 from=translated src=- shape=8e8057c5 vocab=3a2536b0
-/
theorem badPairCount_comm {n : ℕ}
    (A B : Finset (BooleanSpace n)) :
    badPairCount A B = badPairCount B A := by
  classical
  simp only [badPairCount, badCount, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [dot_comm]

/-- Removing points can reduce a bad count by at most the number removed.
@isnad1 id=le.1h4v.s6.ed84f80fe0f9 from=translated src=- shape=8bd3ac4d vocab=0a455457
-/
theorem badCount_le_badCount_add_sdiff {n : ℕ}
    {X L : Finset (BooleanSpace n)} (hXL : X ⊆ L)
    (y : BooleanSpace n) :
    badCount L y ≤ badCount X y + (L \ X).card := by
  classical
  have hsub :
      L.filter (fun z ↦ dot z y = 1) ⊆
        X.filter (fun z ↦ dot z y = 1) ∪ (L \ X) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hz ⊢
    by_cases hzX : z ∈ X
    · exact Or.inl ⟨hzX, hz.2⟩
    · exact Or.inr ⟨hz.1, hzX⟩
  calc
    badCount L y ≤
        (X.filter (fun z ↦ dot z y = 1) ∪ (L \ X)).card :=
      Finset.card_le_card hsub
    _ ≤ (X.filter fun z ↦ dot z y = 1).card + (L \ X).card :=
      Finset.card_union_le _ _
    _ = badCount X y + (L \ X).card := rfl

/-- A coarse upper bound for the high-bias sumset.
@isnad1 id=le.6h5v.s7.ccd7f43e1d89 from=translated src=- shape=b5c617e9 vocab=762a6581
-/
theorem numerical_sumset_upper
    {q a b N y : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100)
    (ha : 0 < a) (hy : 0 ≤ y)
    (hN : (1 - q) * N ≤ a * b)
    (hparseval : y * (((1 - 4 * q) * a) ^ 2) ≤ N * a) :
    y ≤ (1 + 10 * q) * b := by
  have hq1 : 0 ≤ 1 - q := by linarith
  have hcancelA :
      y * (1 - 4 * q) ^ 2 * a ≤ N := by
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      (y * (1 - 4 * q) ^ 2 * a) * a =
          y * (((1 - 4 * q) * a) ^ 2) := by ring
      _ ≤ N * a := hparseval
  have htoB :
      (1 - q) * (y * (1 - 4 * q) ^ 2) ≤ b := by
    apply (mul_le_mul_iff_right₀ ha).mp
    calc
      a * ((1 - q) * (y * (1 - 4 * q) ^ 2)) =
          (1 - q) * (y * (1 - 4 * q) ^ 2 * a) := by ring
      _ ≤ (1 - q) * N :=
        mul_le_mul_of_nonneg_left hcancelA hq1
      _ ≤ a * b := hN
  have h3 : 0 ≤ 3 - 2 * q := by linarith
  have hpoly : 0 ≤ 8 * q ^ 2 * (3 - 2 * q) :=
    mul_nonneg (by positivity) h3
  have hdenom :
      1 - 9 * q ≤ (1 - q) * (1 - 4 * q) ^ 2 := by
    nlinarith
  have h90 : 0 ≤ 1 - 90 * q := by linarith
  have hscalePoly : 0 ≤ q * (1 - 90 * q) :=
    mul_nonneg hq0 h90
  have hscale : 1 ≤ (1 + 10 * q) * (1 - 9 * q) := by
    nlinarith
  calc
    y = 1 * y := by ring
    _ ≤ ((1 + 10 * q) * (1 - 9 * q)) * y :=
      mul_le_mul_of_nonneg_right hscale hy
    _ ≤ (1 + 10 * q) *
        ((1 - q) * (y * (1 - 4 * q) ^ 2)) := by
      have h10 : 0 ≤ 1 + 10 * q := by linarith
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ h10
      calc
        (1 - 9 * q) * y ≤
            ((1 - q) * (1 - 4 * q) ^ 2) * y :=
          mul_le_mul_of_nonneg_right hdenom hy
        _ = (1 - q) * (y * (1 - 4 * q) ^ 2) := by ring
    _ ≤ (1 + 10 * q) * b :=
      mul_le_mul_of_nonneg_left htoB (by linarith)

/-- Saturation and a large subgroup force its orthogonal complement to be small.
@isnad1 id=le.8h7v.s7.3b2ae8ebabd7 from=translated src=- shape=242fecb4 vocab=8b7124b8
-/
theorem numerical_perp_upper
    {q a b N x l c : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hsat : (1 - q) * N ≤ a * b)
    (hx : (1 - q) * b ≤ x) (hxl : x ≤ l)
    (hcard : l * c = N) :
    c ≤ (1 + 3 * q) * a := by
  have hq1 : 0 ≤ 1 - q := by linarith
  have hlower : (1 - q) * b ≤ l := hx.trans hxl
  have hcN : c * ((1 - q) * b) ≤ N := by
    calc
      c * ((1 - q) * b) ≤ c * l :=
        mul_le_mul_of_nonneg_left hlower hc
      _ = N := by nlinarith [hcard]
  have hpreCancel :
      ((1 - q) ^ 2 * c) * b ≤ a * b := by
    calc
      ((1 - q) ^ 2 * c) * b =
          (1 - q) * (c * ((1 - q) * b)) := by ring
      _ ≤ (1 - q) * N :=
        mul_le_mul_of_nonneg_left hcN hq1
      _ ≤ a * b := hsat
  have hbase : (1 - q) ^ 2 * c ≤ a :=
    (mul_le_mul_iff_left₀ hb).mp hpreCancel
  have hinside : 0 ≤ 1 - 5 * q + 3 * q ^ 2 := by
    nlinarith [sq_nonneg q]
  have hscalePoly :
      0 ≤ q * (1 - 5 * q + 3 * q ^ 2) :=
    mul_nonneg hq0 hinside
  have hscale : 1 ≤ (1 + 3 * q) * (1 - q) ^ 2 := by
    nlinarith
  calc
    c = 1 * c := by ring
    _ ≤ ((1 + 3 * q) * (1 - q) ^ 2) * c :=
      mul_le_mul_of_nonneg_right hscale hc
    _ = (1 + 3 * q) * ((1 - q) ^ 2 * c) := by ring
    _ ≤ (1 + 3 * q) * a :=
      mul_le_mul_of_nonneg_left hbase (by linarith)

/--
@isnad1 id=le.0h3v.s5.a3dc2b71d1ba from=translated src=- shape=58c4775a vocab=385a9b8c
-/
theorem card_symmDiff_le_sdiff_add_sdiff {α : Type*}
    [DecidableEq α] (S T : Finset α) :
    (S ∆ T).card ≤ (S \ T).card + (T \ S).card := by
  rw [Finset.symmDiff_def]
  exact Finset.card_union_le _ _

/--
@isnad1 id=le.2h4v.s6.b1829179789d from=translated src=- shape=759485a2 vocab=385a9b8c
-/
theorem card_symmDiff_le_of_common_subset {α : Type*}
    [DecidableEq α] {X S T : Finset α}
    (hXS : X ⊆ S) (hXT : X ⊆ T) :
    (S ∆ T).card ≤ (S \ X).card + (T \ X).card := by
  calc
    (S ∆ T).card ≤ (S \ T).card + (T \ S).card :=
      card_symmDiff_le_sdiff_add_sdiff S T
    _ ≤ (S \ X).card + (T \ X).card := by
      apply Nat.add_le_add
      · apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_sdiff] at hz ⊢
        exact ⟨hz.1, fun hzX ↦ hz.2 (hXT hzX)⟩
      · apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_sdiff] at hz ⊢
        exact ⟨hz.1, fun hzX ↦ hz.2 (hXS hzX)⟩

/--
Quantitative saturated almost-orthogonality on the Boolean cube.

The hypotheses use counts rather than probabilities, so no nonzero
denominators are hidden.  The constants are deliberately coarse.
@isnad1 id=ex.6h4v.s9.7e5cffb9e223 from=translated src=- shape=060eecdb vocab=fabd756a
-/
theorem saturated_almost_orthogonality {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hA : A.Nonempty) (hzero : 0 ∈ B)
    (hsat :
      (1 - q) * Fintype.card (BooleanSpace n) ≤
        (A.card : ℝ) * B.card)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    ∃ L : Submodule (ZMod 2) (BooleanSpace n),
      (((A ∆ submodulePoints (perp L)).card : ℝ) ≤
          5 * q * A.card) ∧
      (((B ∆ submodulePoints L).card : ℝ) ≤
          12 * q * B.card) := by
  classical
  let X := lowBiasSet A B q
  have hXzero : 0 ∈ X := zero_mem_lowBiasSet A B hzero hq0.le
  have hXsubB : X ⊆ B := lowBiasSet_subset_right A B q
  have hdouble :=
    lowBiasSet_doubling_lt_three_halves A B hq0 hq hA hzero hsat hbad
  obtain ⟨L, hLset⟩ := small_sumset_is_submodule X (by simpa [X] using hdouble)
  let LF := submodulePoints L
  let C := submodulePoints (perp L)
  have hLF : LF = X + X := by
    ext z
    change z ∈ submodulePoints L ↔ z ∈ X + X
    rw [mem_submodulePoints]
    exact Set.ext_iff.mp hLset z
  have hXsubL : X ⊆ LF := by
    intro z hz
    rw [hLF]
    exact Finset.mem_add.mpr ⟨z, hz, 0, hXzero, by simp⟩
  have hApos : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hBnonempty : B.Nonempty := ⟨0, hzero⟩
  have hBpos : (0 : ℝ) < B.card := by
    exact_mod_cast hBnonempty.card_pos
  have hXlower :
      (1 - q) * (B.card : ℝ) ≤ X.card := by
    simpa [X] using card_lowBiasSet_lower A B hq0 hA hbad
  have hparseval :
      ((LF.card : ℝ) * (((1 - 4 * q) * A.card) ^ 2)) ≤
        (Fintype.card (BooleanSpace n) : ℝ) * A.card := by
    simpa [hLF, X] using
      lowBiasSet_sum_card_bound A B hq0.le (by linarith : 4 * q ≤ 1)
  have hLupper :
      (LF.card : ℝ) ≤ (1 + 10 * q) * B.card := by
    apply numerical_sumset_upper
      (q := q) (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (N := (Fintype.card (BooleanSpace n) : ℝ))
      (y := (LF.card : ℝ)) hq0.le hq hApos
      (by positivity) hsat hparseval
  have hBX :
      ((B \ X).card : ℝ) = B.card - X.card := by
    rw [Finset.card_sdiff_of_subset hXsubB,
      Nat.cast_sub (Finset.card_mono hXsubB)]
  have hLX :
      ((LF \ X).card : ℝ) = LF.card - X.card := by
    rw [Finset.card_sdiff_of_subset hXsubL,
      Nat.cast_sub (Finset.card_mono hXsubL)]
  have hsymmB :
      ((B ∆ LF).card : ℝ) ≤ 12 * q * B.card := by
    have hcommon :=
      card_symmDiff_le_of_common_subset hXsubB hXsubL
    have hcommonR :
        ((B ∆ LF).card : ℝ) ≤
          (B \ X).card + (LF \ X).card := by
      exact_mod_cast hcommon
    nlinarith
  have hcardLC :
      (LF.card : ℝ) * C.card =
        Fintype.card (BooleanSpace n) := by
    have hnat := submodulePoints_perp_card_mul L
    rw [card_booleanSpace]
    exact_mod_cast (by simpa [LF, C] using hnat)
  have hCupper :
      (C.card : ℝ) ≤ (1 + 3 * q) * A.card := by
    apply numerical_perp_upper
      (q := q) (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (N := (Fintype.card (BooleanSpace n) : ℝ))
      (x := (X.card : ℝ)) (l := (LF.card : ℝ))
      (c := (C.card : ℝ)) hq0.le hq hBpos (by positivity)
      hsat hXlower
    · exact_mod_cast Finset.card_mono hXsubL
    · exact hcardLC
  have hthirdR :
      (3 : ℝ) * (LF \ X).card ≤ X.card := by
    nlinarith
  have hthird :
      3 * (LF \ X).card ≤ X.card := by
    exact_mod_cast hthirdR
  have hpoint : ∀ a ∈ A \ C,
      X.card ≤ 3 * badCount X a := by
    intro a ha
    have haC : a ∉ C := (Finset.mem_sdiff.mp ha).2
    have haNot : a ∉ perp L := by
      simpa [C] using haC
    have hhalf := two_mul_badCount_submodulePoints L a haNot
    have hremove := badCount_le_badCount_add_sdiff hXsubL a
    have hLXnat := Finset.card_sdiff_add_card_eq_card hXsubL
    change 2 * badCount LF a = LF.card at hhalf
    omega
  have hsumLower :
      (A \ C).card * X.card ≤ 3 * badPairCount A X := by
    calc
      (A \ C).card * X.card =
          ∑ a ∈ A \ C, X.card := by simp
      _ ≤ ∑ a ∈ A \ C, 3 * badCount X a :=
        Finset.sum_le_sum fun a ha ↦ hpoint a ha
      _ ≤ ∑ a ∈ A, 3 * badCount X a := by
        apply Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ = 3 * badPairCount X A := by
        simp [badPairCount, Finset.mul_sum]
      _ = 3 * badPairCount A X := by
        rw [badPairCount_comm]
  have hbadAX :
      (badPairCount A X : ℝ) ≤ q ^ 2 * A.card * B.card := by
    calc
      (badPairCount A X : ℝ) ≤ badPairCount A B := by
        exact_mod_cast (show badPairCount A X ≤ badPairCount A B by
          apply Finset.sum_le_sum_of_subset hXsubB)
      _ ≤ q ^ 2 * A.card * B.card := hbad
  have hsumLowerR :
      ((A \ C).card : ℝ) * X.card ≤
        3 * q ^ 2 * A.card * B.card := by
    have hcast :
        ((A \ C).card : ℝ) * X.card ≤
          3 * (badPairCount A X : ℝ) := by
      exact_mod_cast hsumLower
    nlinarith
  have hpreCancel :
      (((A \ C).card : ℝ) * (1 - q)) * B.card ≤
        (3 * q ^ 2 * A.card) * B.card := by
    calc
      (((A \ C).card : ℝ) * (1 - q)) * B.card =
          ((A \ C).card : ℝ) * ((1 - q) * B.card) := by ring
      _ ≤ ((A \ C).card : ℝ) * X.card :=
        mul_le_mul_of_nonneg_left hXlower (by positivity)
      _ ≤ 3 * q ^ 2 * A.card * B.card := hsumLowerR
      _ = (3 * q ^ 2 * A.card) * B.card := by ring
  have hcancel :
      ((A \ C).card : ℝ) * (1 - q) ≤
        3 * q ^ 2 * A.card :=
    (mul_le_mul_iff_left₀ hBpos).mp hpreCancel
  have hcoef : 3 * q ^ 2 ≤ q * (1 - q) := by
    nlinarith [sq_nonneg q]
  have hOutside :
      ((A \ C).card : ℝ) ≤ q * A.card := by
    have hq1 : 0 < 1 - q := by linarith
    apply (mul_le_mul_iff_right₀ hq1).mp
    calc
      (1 - q) * (A \ C).card =
          ((A \ C).card : ℝ) * (1 - q) := by ring
      _ ≤ 3 * q ^ 2 * A.card := hcancel
      _ ≤ (q * (1 - q)) * A.card :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (1 - q) * (q * A.card) := by ring
  have hpartA :
      ((A \ C).card : ℝ) + (A ∩ C).card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A C
  have hpartC :
      ((C \ A).card : ℝ) + (C ∩ A).card = C.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter C A
  have hinter : (C ∩ A).card = (A ∩ C).card := by
    rw [Finset.inter_comm]
  have hinterR :
      ((C ∩ A).card : ℝ) = (A ∩ C).card := by
    exact_mod_cast hinter
  have hsymmA :
      ((A ∆ C).card : ℝ) ≤ 5 * q * A.card := by
    have hsymm :=
      card_symmDiff_le_sdiff_add_sdiff A C
    have hsymmR :
        ((A ∆ C).card : ℝ) ≤
          (A \ C).card + (C \ A).card := by
      exact_mod_cast hsymm
    linarith only [hsymmR, hpartA, hpartC, hinterR, hCupper, hOutside]
  refine ⟨L, ?_, ?_⟩
  · simpa [C] using hsymmA
  · simpa [LF] using hsymmB

end

end RobustInverseUncertainty
