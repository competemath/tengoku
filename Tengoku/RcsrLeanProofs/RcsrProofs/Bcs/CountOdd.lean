/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Metric
import Tengoku.Seed.Data.Int.Interval
import Tengoku.Seed.Data.Finset.Prod
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Odd-parity level-set cardinalities of the bcs distance functions

`D2, D3, D4, D8` are always odd. This file computes the exact cardinality of
each level set `{(x,y,z) : f x y z = n}` (boxed to `Icc (-n) n`, a valid
superset since all affine forms defining `f` have coefficients ±2, so any
solution has `|x|,|y|,|z| ≤ n`).

## Strategy

`D2 x y z` factors as `max(|2s-1|, |2u-1|, |2v-1|)` for `s = x+y+z`,
`u = x-y+z`, `v = -x+y+z` (an `omega`-checkable algebraic identity: the six
affine forms defining `D2` are exactly `±(2s-1), ±(2u-1), ±(2v-1)`). The
change of variables `(x,y,z) ↦ (s,u,v)` is an injective linear
reparametrization onto the same-parity sublattice of `ℤ³` (rational inverse
`x=(s-v)/2, y=(s-u)/2, z=(u+v)/2`), formalized once as the reusable
`card_xyz_uvw` lemma. Counting `{max(|2s-1|,|2u-1|,|2v-1|) = n}` is then a
ball-difference: it equals `(box of radius ≤ n) minus (box of radius ≤ n-2)`,
since `2s-1` etc. are always odd so the max only takes odd values, and each
single-coordinate constraint `|2s-1| ≤ n` pins `s` to an explicit interval of
`2k+2` consecutive integers (`n = 2k+1`) with exactly `k+1` values of each
parity, giving a clean `2*(k+1)^3` closed form for the ball.

`D3, D4` reduce to `D2` by exact pointwise identities (coordinate
permutations with a sign flip, reflecting the crystal's 3-fold symmetry).
`D8` factors the same way as `D2` (shifted constants `1,3,3` instead of
`1,1,1`) after subtracting its exceptional `+2` bump term; the bump affects
only the line `x=y, z=1-x`, on which the unbumped function reduces to
`|2t+1|` — so it contributes a clean ±2 correction at each level.
-/

namespace Bcs
namespace CountOdd

open Finset

/-- Cardinality of the level set `{(x,y,z) ∈ Icc(-n,n)³ : f x y z = n}`.-/
def levelCard (f : Int → Int → Int → Int) (n : Nat) : Nat :=
  ((Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
    (fun p => f p.1 p.2.1 p.2.2 = (n : Int))).card

/-! ## Parity of the four classes -/

theorem D2_odd (x y z : Int) : D2 x y z % 2 = 1 := by unfold D2; omega
theorem D3_odd (x y z : Int) : D3 x y z % 2 = 1 := by unfold D3; omega
theorem D4_odd (x y z : Int) : D4 x y z % 2 = 1 := by unfold D4; omega
theorem D8_odd (x y z : Int) : D8 x y z % 2 = 1 := by unfold D8; split <;> omega

theorem D2_nonneg (x y z : Int) : 0 ≤ D2 x y z := by unfold D2; omega
theorem D8_nonneg (x y z : Int) : 0 ≤ D8 x y z := by unfold D8; split <;> omega

/-! ## Even n: all four level sets are empty -/

theorem levelCard_D2_even (n : Nat) (hn : n % 2 = 0) : levelCard D2 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D2_odd x y z
  intro heq; rw [heq] at h; omega

theorem levelCard_D3_even (n : Nat) (hn : n % 2 = 0) : levelCard D3 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D3_odd x y z
  intro heq; rw [heq] at h; omega

theorem levelCard_D4_even (n : Nat) (hn : n % 2 = 0) : levelCard D4 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D4_odd x y z
  intro heq; rw [heq] at h; omega

theorem levelCard_D8_even (n : Nat) (hn : n % 2 = 0) : levelCard D8 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D8_odd x y z
  intro heq; rw [heq] at h; omega

/-! ## Small cases by kernel computation -/

theorem levelCard_D2_1 : levelCard D2 1 = 2 := by decide +kernel
theorem levelCard_D3_1 : levelCard D3 1 = 2 := by decide +kernel
theorem levelCard_D4_1 : levelCard D4 1 = 2 := by decide +kernel
theorem levelCard_D8_1 : levelCard D8 1 = 0 := by decide +kernel
theorem levelCard_D2_3 : levelCard D2 3 = 14 := by decide +kernel
theorem levelCard_D8_3 : levelCard D8 3 = 14 := by decide +kernel

/-! ## `D3`, `D4` reduce to `D2` by exact coordinate identities -/

theorem D3_eq_D2 (x y z : Int) : D3 x y z = D2 (-x) z y := by unfold D2 D3; omega
theorem D4_eq_D2 (x y z : Int) : D4 x y z = D2 (-y) z x := by unfold D2 D4; omega

set_option maxHeartbeats 1000000 in
theorem levelCard_D3_eq_D2 (n : ℕ) : levelCard D3 n = levelCard D2 n := by
  unfold levelCard
  apply Finset.card_nbij' (fun p => (-p.1, p.2.2, p.2.1)) (fun p => (-p.1, p.2.2, p.2.1))
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy, hz⟩, heq⟩ := hp
    refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    rw [← heq, D3_eq_D2 x y z]
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy, hz⟩, heq⟩ := hp
    refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    rw [← heq]
    have := D3_eq_D2 (-x) z y
    simp only [neg_neg] at this
    rw [this]
  · rintro ⟨x, y, z⟩ _; simp
  · rintro ⟨x, y, z⟩ _; simp

set_option maxHeartbeats 1000000 in
theorem levelCard_D4_eq_D2 (n : ℕ) : levelCard D4 n = levelCard D2 n := by
  unfold levelCard
  apply Finset.card_nbij' (fun p => (-p.2.1, p.2.2, p.1)) (fun p => (p.2.2, -p.1, p.2.1))
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy, hz⟩, heq⟩ := hp
    refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    rw [← heq, D4_eq_D2 x y z]
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy, hz⟩, heq⟩ := hp
    refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    rw [← heq]
    have := D4_eq_D2 z (-x) y
    simp only [neg_neg] at this
    rw [this]
  · rintro ⟨x, y, z⟩ _; simp
  · rintro ⟨x, y, z⟩ _; simp

/-! ## Change-of-variables toolkit: `(x,y,z) ↦ (x+y+z, x-y+z, -x+y+z)`

Transfers a filtered count over the `(x,y,z)` box to a filtered count over an
`(s,u,v)` box carrying the same-parity constraint, given confinement of the
predicate to both boxes (any box big enough works — the two radii `n`, `N`
need not match, which lets us always pick `N` generously large). -/

theorem card_xyz_uvw (n N : ℕ) (F : Int → Int → Int → Prop)
    [∀ s u v, Decidable (F s u v)]
    (hxyz : ∀ x y z : Int, F (x + y + z) (x - y + z) (-x + y + z) →
      x ∈ Icc (-(n : Int)) n ∧ y ∈ Icc (-(n : Int)) n ∧ z ∈ Icc (-(n : Int)) n)
    (huvw : ∀ s u v : Int, F s u v →
      s ∈ Icc (-(N : Int)) N ∧ u ∈ Icc (-(N : Int)) N ∧ v ∈ Icc (-(N : Int)) N) :
    ((Icc (-(n : Int)) n ×ˢ Icc (-(n : Int)) n ×ˢ Icc (-(n : Int)) n).filter
        fun p => F (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2) (-p.1 + p.2.1 + p.2.2)).card
      = ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
          fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
            F q.1 q.2.1 q.2.2).card := by
  refine Finset.card_bij'
    (fun p _ => (p.1 + p.2.1 + p.2.2, p.1 - p.2.1 + p.2.2, -p.1 + p.2.1 + p.2.2))
    (fun q _ => ((q.1 - q.2.2) / 2, (q.1 - q.2.1) / 2, (q.2.1 + q.2.2) / 2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp ⊢
    obtain ⟨-, hF⟩ := hp
    obtain ⟨hs, hu, hv⟩ := huvw _ _ _ hF
    simp only [mem_Icc] at hs hu hv
    exact ⟨⟨hs, hu, hv⟩, ⟨by omega, by omega⟩, hF⟩
  · rintro ⟨s, u, v⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq ⊢
    obtain ⟨-, ⟨hp1, hp2⟩, hF⟩ := hq
    have hx : (s - v) / 2 + (s - u) / 2 + (u + v) / 2 = s := by omega
    have hy : (s - v) / 2 - (s - u) / 2 + (u + v) / 2 = u := by omega
    have hz : -((s - v) / 2) + (s - u) / 2 + (u + v) / 2 = v := by omega
    rw [hx, hy, hz]
    obtain ⟨hxb, hyb, hzb⟩ := hxyz ((s - v) / 2) ((s - u) / 2) ((u + v) / 2)
      (by rw [hx, hy, hz]; exact hF)
    simp only [mem_Icc] at hxb hyb hzb
    exact ⟨⟨hxb, hyb, hzb⟩, hF⟩
  · rintro ⟨x, y, z⟩ _
    have h1 : (x + y + z - (-x + y + z)) / 2 = x := by omega
    have h2 : (x + y + z - (x - y + z)) / 2 = y := by omega
    have h3 : (x - y + z + (-x + y + z)) / 2 = z := by omega
    simp only [h1, h2, h3]
  · rintro ⟨s, u, v⟩ hq
    simp only [mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨-, ⟨hp1, hp2⟩, -⟩ := hq
    have h1 : (s - v) / 2 + (s - u) / 2 + (u + v) / 2 = s := by omega
    have h2 : (s - v) / 2 - (s - u) / 2 + (u + v) / 2 = u := by omega
    have h3 : -((s - v) / 2) + (s - u) / 2 + (u + v) / 2 = v := by omega
    simp only [h1, h2, h3]

/-! ## `D2`'s diagonalization: `D2 x y z = max(|2s-1|,|2u-1|,|2v-1|)` -/

/-- `F2 n s u v` holds iff `max(|2s-1|,|2u-1|,|2v-1|) = n`, stated without
`abs`/`max` (all six affine forms defining `D2` are `±(2s-1), ±(2u-1),
±(2v-1)`, so this is an `omega`-checkable reformulation).-/
def F2 (n s u v : Int) : Prop :=
  ((-n ≤ 2 * s - 1 ∧ 2 * s - 1 ≤ n) ∧ (-n ≤ 2 * u - 1 ∧ 2 * u - 1 ≤ n) ∧
      (-n ≤ 2 * v - 1 ∧ 2 * v - 1 ≤ n)) ∧
    (2 * s - 1 = n ∨ -(2 * s - 1) = n ∨ 2 * u - 1 = n ∨ -(2 * u - 1) = n ∨
      2 * v - 1 = n ∨ -(2 * v - 1) = n)

instance (n s u v : Int) : Decidable (F2 n s u v) := by unfold F2; infer_instance

theorem D2_eq_F2 (x y z n : Int) : D2 x y z = n ↔ F2 n (x + y + z) (x - y + z) (-x + y + z) := by
  unfold D2 F2; omega

theorem levelCard_D2_eq_uvw (n : ℕ) :
    levelCard D2 n =
      ((Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int)).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F2 (n : Int) q.1 q.2.1 q.2.2).card := by
  unfold levelCard
  have hfilt : (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter (fun p => D2 p.1 p.2.1 p.2.2 = (n : Int))
      = (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
        (fun p => F2 (n : Int) (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2)
          (-p.1 + p.2.1 + p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    exact D2_eq_F2 p.1 p.2.1 p.2.2 n
  rw [hfilt]
  apply card_xyz_uvw n (2 * n + 2) (F2 (n : Int))
  · intro x y z hF
    unfold F2 at hF
    simp only [mem_Icc]
    omega
  · intro s u v hF
    unfold F2 at hF
    simp only [mem_Icc]
    omega

/-! ## Ball-difference count for `F2`

`F2 n s u v` says all three of `|2s-1|,|2u-1|,|2v-1|` are `≤ n` and at least
one equals `n`. Since these three quantities are always odd, as `n` increases
by `2` the "all `≤ n`" ball grows by exactly the "at least one `= n`" shell
(no values are skipped), so the `F2`-count at `n` is a ball-difference:
`ball n - ball (n-2)`. -/

/-- The "ball": same-parity triples in a box of radius `N` with all three of
`|2s-1|,|2u-1|,|2v-1| ≤ n`.-/
def ballF2 (N n : ℕ) : Finset (Int × Int × Int) :=
  ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
    (fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
      (-(n : Int) ≤ 2 * q.1 - 1 ∧ 2 * q.1 - 1 ≤ n) ∧
      (-(n : Int) ≤ 2 * q.2.1 - 1 ∧ 2 * q.2.1 - 1 ≤ n) ∧
      (-(n : Int) ≤ 2 * q.2.2 - 1 ∧ 2 * q.2.2 - 1 ≤ n)))

theorem ballF2_mono (N : ℕ) {m n : ℕ} (h : m ≤ n) : ballF2 N m ⊆ ballF2 N n := by
  unfold ballF2
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨hbox, hpar, hs, hu, hv⟩ := hp
  exact ⟨hbox, hpar, by omega, by omega, by omega⟩

/-- One-dimensional count: `#{v ∈ Icc(-N,N) : v ≡ r (mod 2), -(n:Int) ≤ 2v-1 ≤ n}`.-/
theorem even_count_in_interval (k : ℕ) :
    ((Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 0)).card = k + 1 := by
  induction k with
  | zero => decide
  | succ m ih =>
    have hexp : (Finset.Icc (-((m : Int) + 1)) ((m : Int) + 1 + 1))
        = insert (-((m : Int) + 1)) (insert ((m : Int) + 2) (Finset.Icc (-(m : Int)) (m + 1 : Int))) := by
      ext v; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    push_cast
    rw [hexp, Finset.filter_insert, Finset.filter_insert]
    rcases Int.emod_two_eq (m : Int) with hm | hm
    · have h1 : ¬ ((-((m : Int) + 1)) % 2 = 0) := by omega
      have h2 : ((m : Int) + 2) % 2 = 0 := by omega
      simp only [h1, h2, ite_false, ite_true]
      rw [Finset.card_insert_of_notMem, ih]
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · have h1 : ((-((m : Int) + 1)) % 2 = 0) := by omega
      have h2 : ¬ (((m : Int) + 2) % 2 = 0) := by omega
      simp only [h1, h2, ite_false, ite_true]
      rw [Finset.card_insert_of_notMem, ih]
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem odd_count_in_interval (k : ℕ) :
    ((Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 1)).card = k + 1 := by
  have htot : (Finset.Icc (-(k : Int)) (k + 1 : Int)).card = 2 * k + 2 := by
    rw [Int.card_Icc]; omega
  have hsplit : (Finset.Icc (-(k : Int)) (k + 1 : Int))
      = (Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 0) ∪
        (Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 1) := by
    ext v; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_filter]; omega
  have hdisj : Disjoint ((Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 0))
      ((Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 1)) := by
    rw [Finset.disjoint_filter]
    intro v _ hv0 hv1
    omega
  have := Finset.card_union_of_disjoint hdisj
  rw [← hsplit, htot, even_count_in_interval] at this
  omega

/-- The single-coordinate constraint `-(n:Int) ≤ 2v-1 ≤ n` for `n = 2k+1` pins
`v` to exactly the interval `Icc (-k) (k+1)`.-/
theorem coord_constraint_iff (k : ℕ) (v : Int) :
    (-((2 * k + 1 : ℕ) : Int) ≤ 2 * v - 1 ∧ 2 * v - 1 ≤ ((2 * k + 1 : ℕ) : Int)) ↔
      -(k : Int) ≤ v ∧ v ≤ (k : Int) + 1 := by
  omega

set_option maxRecDepth 2000 in
/-- The `F2`-count (within a box of radius `N`) equals the ball-difference:
`F2 n` holds exactly on the same-parity triples that are in `ball N n` but not
in `ball N (n-2)`.-/
theorem F2Card_eq_ball_diff (N k : ℕ) (hN : 2 * k + 1 ≤ N) :
    ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F2 ((2 * k + 1 : ℕ) : Int) q.1 q.2.1 q.2.2).card
      = (ballF2 N (2 * k + 1)).card - (ballF2 N (2 * k - 1)).card := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Nat.mul_zero, Nat.zero_add]
    have hempty : ballF2 N (2 * 0 - 1) = ∅ := by
      unfold ballF2
      apply Finset.filter_false_of_mem
      rintro ⟨a, b, c⟩ _ ⟨-, hsa, -, -⟩
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.sub_zero]
    congr 1
    unfold ballF2
    apply Finset.filter_congr
    intro p _
    unfold F2
    constructor
    · rintro ⟨hpar, hbound, hor⟩
      exact ⟨hpar, hbound⟩
    · rintro ⟨hpar, hbound⟩
      exact ⟨hpar, hbound, by omega⟩
  · have hsub : ballF2 N (2 * k - 1) ⊆ ballF2 N (2 * k + 1) :=
      ballF2_mono N (by omega)
    have hcard_diff : (ballF2 N (2 * k + 1)).card - (ballF2 N (2 * k - 1)).card
        = ((ballF2 N (2 * k + 1)) \ (ballF2 N (2 * k - 1))).card := by
      rw [Finset.card_sdiff_of_subset hsub]
    rw [hcard_diff]
    congr 1
    unfold ballF2
    ext ⟨a, b, c⟩
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    unfold F2
    constructor
    · rintro ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, hor⟩
      refine ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound⟩, ?_⟩
      rintro ⟨-, -, hsa, hsb, hsc⟩
      omega
    · rintro ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound⟩, hnotin⟩
      refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, ?_⟩
      by_contra hor
      push Not at hor
      apply hnotin
      refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩ <;> omega

/-! ## `D8`: unbumped base, diagonalization, and the bump-line correction

`D8 x y z = D8base x y z + (2 if x = y ∧ z = 1-x else 0)`, where `D8base` is
the max of the same six affine forms as `D2` but shifted by `1, 3, 3` instead
of `1, 1, 1`: `D8base x y z = max(|2s-1|, |2u-3|, |2v-3|)` in the same
`(s,u,v) = (x+y+z, x-y+z, -x+y+z)` coordinates. The shifted bound `|2u-3| ≤ n`
pins `u` to the interval `Icc (1-k) (k+2)` (for `n = 2k+1`) instead of
`Icc (-k) (k+1)` — a translate by `1`, so it contains the same number of
even/odd values (`k+1` each), giving `D8base` the *same* ball formula
`2*(k+1)^3` as `D2`. Restricted to the bump line `x=y=t, z=1-t`, `D8base`
reduces to `|2t+1|` (an exact computation: `s=t+1`, `u=v=1-t`, so
`2s-1 = 2t+1` and `2u-3 = 2v-3 = -2t-1`), which takes every odd value `≥ 1`
exactly twice and no even value — giving the exact `∓2` bump correction. -/

def D8base (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z - 1) <| max (2*x - 2*y + 2*z - 3) <| max (-2*x + 2*y + 2*z - 3) <|
    max (-2*x - 2*y - 2*z + 1) <| max (2*x - 2*y - 2*z + 3) (-2*x + 2*y - 2*z + 3)

theorem D8_eq_base_add_bump (x y z : Int) :
    D8 x y z = D8base x y z + (if x = y ∧ z = 1 - x then 2 else 0) := by
  unfold D8 D8base; rfl

theorem D8base_odd (x y z : Int) : D8base x y z % 2 = 1 := by unfold D8base; omega
theorem D8base_nonneg (x y z : Int) : 0 ≤ D8base x y z := by unfold D8base; omega

theorem D8base_line (t : Int) : D8base t t (1 - t) = max (2 * t + 1) (-(2 * t + 1)) := by
  unfold D8base; omega

/-- `F8 n s u v` holds iff `max(|2s-1|,|2u-3|,|2v-3|) = n` (abs-free, matching
`D8base`'s shifted-by-`1,3,3` version of `D2`'s diagonalization).-/
def F8 (n s u v : Int) : Prop :=
  ((-n ≤ 2 * s - 1 ∧ 2 * s - 1 ≤ n) ∧ (-n ≤ 2 * u - 3 ∧ 2 * u - 3 ≤ n) ∧
      (-n ≤ 2 * v - 3 ∧ 2 * v - 3 ≤ n)) ∧
    (2 * s - 1 = n ∨ -(2 * s - 1) = n ∨ 2 * u - 3 = n ∨ -(2 * u - 3) = n ∨
      2 * v - 3 = n ∨ -(2 * v - 3) = n)

instance (n s u v : Int) : Decidable (F8 n s u v) := by unfold F8; infer_instance

theorem D8base_eq_F8 (x y z n : Int) :
    D8base x y z = n ↔ F8 n (x + y + z) (x - y + z) (-x + y + z) := by
  unfold D8base F8; omega

def levelCard8base (n : Nat) : Nat :=
  ((Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
    (fun p => D8base p.1 p.2.1 p.2.2 = (n : Int))).card

theorem levelCard8base_eq_uvw (n : ℕ) (hn : 3 ≤ n) :
    levelCard8base n =
      ((Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int)).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F8 (n : Int) q.1 q.2.1 q.2.2).card := by
  unfold levelCard8base
  have hfilt : (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter (fun p => D8base p.1 p.2.1 p.2.2 = (n : Int))
      = (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
        (fun p => F8 (n : Int) (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2)
          (-p.1 + p.2.1 + p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    exact D8base_eq_F8 p.1 p.2.1 p.2.2 n
  rw [hfilt]
  apply card_xyz_uvw n (2 * n + 2) (F8 (n : Int))
  · intro x y z hF
    unfold F8 at hF
    simp only [mem_Icc]
    omega
  · intro s u v hF
    unfold F8 at hF
    simp only [mem_Icc]
    omega

/-- The `u`-coordinate's shifted interval `Icc (1-k) (k+2)` contains the same
number of even values (`k+1`) as `Icc (-k) (k+1)` — a translate by `1` of an
interval swaps which parity sits at which end but preserves the split.-/
theorem even_count_in_interval_shift (k : ℕ) :
    ((Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 0)).card = k + 1 := by
  have heq : (Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 0)
      = ((Finset.Icc (-(k : Int)) (k + 1 : Int)).filter (fun v => v % 2 = 1)).image
        (fun v => v + 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨v - 1, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨w, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      omega
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => by omega), odd_count_in_interval]

theorem odd_count_in_interval_shift (k : ℕ) :
    ((Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 1)).card = k + 1 := by
  have htot : (Finset.Icc (1 - (k : Int)) (k + 2 : Int)).card = 2 * k + 2 := by
    rw [Int.card_Icc]; omega
  have hsplit : (Finset.Icc (1 - (k : Int)) (k + 2 : Int))
      = (Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 0) ∪
        (Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 1) := by
    ext v; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_filter]; omega
  have hdisj : Disjoint ((Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 0))
      ((Finset.Icc (1 - (k : Int)) (k + 2 : Int)).filter (fun v => v % 2 = 1)) := by
    rw [Finset.disjoint_filter]
    intro v _ hv0 hv1
    omega
  have := Finset.card_union_of_disjoint hdisj
  rw [← hsplit, htot, even_count_in_interval_shift] at this
  omega

/-- The "ball" for `D8base`: same-parity triples in a box of radius `N` with
`|2s-1| ≤ n` and `|2u-3|, |2v-3| ≤ n`.-/
def ballF8 (N n : ℕ) : Finset (Int × Int × Int) :=
  ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
    (fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
      (-(n : Int) ≤ 2 * q.1 - 1 ∧ 2 * q.1 - 1 ≤ n) ∧
      (-(n : Int) ≤ 2 * q.2.1 - 3 ∧ 2 * q.2.1 - 3 ≤ n) ∧
      (-(n : Int) ≤ 2 * q.2.2 - 3 ∧ 2 * q.2.2 - 3 ≤ n)))

theorem ballF8_mono (N : ℕ) {m n : ℕ} (h : m ≤ n) : ballF8 N m ⊆ ballF8 N n := by
  unfold ballF8
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨hbox, hpar, hs, hu, hv⟩ := hp
  exact ⟨hbox, hpar, by omega, by omega, by omega⟩

theorem coord_constraint8_u_iff (k : ℕ) (v : Int) :
    (-((2 * k + 1 : ℕ) : Int) ≤ 2 * v - 3 ∧ 2 * v - 3 ≤ ((2 * k + 1 : ℕ) : Int)) ↔
      1 - (k : Int) ≤ v ∧ v ≤ (k : Int) + 2 := by omega

set_option maxRecDepth 2000 in
theorem F8Card_eq_ball_diff (N k : ℕ) (hk : 1 ≤ k) (_hN : 2 * k + 1 ≤ N) :
    ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F8 ((2 * k + 1 : ℕ) : Int) q.1 q.2.1 q.2.2).card
      = (ballF8 N (2 * k + 1)).card - (ballF8 N (2 * k - 1)).card := by
  have hsub : ballF8 N (2 * k - 1) ⊆ ballF8 N (2 * k + 1) := ballF8_mono N (by omega)
  have hcard_diff : (ballF8 N (2 * k + 1)).card - (ballF8 N (2 * k - 1)).card
      = ((ballF8 N (2 * k + 1)) \ (ballF8 N (2 * k - 1))).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  rw [hcard_diff]
  congr 1
  unfold ballF8
  ext ⟨a, b, c⟩
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  unfold F8
  constructor
  · rintro ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, hor⟩
    refine ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound⟩, ?_⟩
    rintro ⟨-, -, hsa, hsb, hsc⟩
    omega
  · rintro ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound⟩, hnotin⟩
    refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, ?_⟩
    by_contra hor
    push Not at hor
    apply hnotin
    refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩ <;> omega

theorem levelCard8base_1 : levelCard8base 1 = 1 := by unfold levelCard8base; decide

/-- On the bump line, the number of points with `D8base = m` (`m` odd `≥ 1`)
is exactly `2` (the two roots of `|2t+1| = m`), and `0` otherwise.-/
theorem lineAtLevel_card (M : Int) (m : ℕ) (hM : (m : Int) + 1 ≤ M) (hm : 1 ≤ m)
    (hodd : m % 2 = 1) :
    ((Finset.Icc (-M) M).filter (fun t => D8base t t (1 - t) = (m : Int))).card = 2 := by
  have heq : (Finset.Icc (-M) M).filter
      (fun t => D8base t t (1 - t) = (m : Int)) = {((m : Int) - 1) / 2, (-(m : Int) - 1) / 2} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      D8base_line]
    omega
  rw [heq]
  have hne : ((m : Int) - 1) / 2 ≠ (-(m : Int) - 1) / 2 := by omega
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

set_option maxHeartbeats 1000000 in
/-- **The bump correction for `D8` at `n ≥ 3`**: for `n = 2k+1` with `k ≥ 1`,
both `n` and `n-2` are odd and `≥ 1`, so the bump line contributes exactly `2`
points removed (bumped from level `n` to `n+2`) and `2` points added (bumped
from level `n-2` into level `n`) — a net-zero correction, so `D8` and `D8base`
have the same level-`n` cardinality.-/
theorem levelCard_D8_eq_base (k : ℕ) (hk : 1 ≤ k) :
    levelCard D8 (2 * k + 1) = levelCard8base (2 * k + 1) := by
  unfold levelCard levelCard8base
  set n : Int := ((2 * k + 1 : ℕ) : Int) with hn
  set A := (Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).filter
      (fun p => D8 p.1 p.2.1 p.2.2 = n) with hA
  set B := (Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).filter
      (fun p => D8base p.1 p.2.1 p.2.2 = n) with hB
  have key : ∀ p : Int × Int × Int, p ∈ A ↔
      (p ∈ B ∧ ¬(p.1 = p.2.1 ∧ p.2.2 = 1 - p.1)) ∨
      (p.1 = p.2.1 ∧ p.2.2 = 1 - p.1 ∧ D8base p.1 p.2.1 p.2.2 = n - 2 ∧
        -n ≤ p.1 ∧ p.1 ≤ n ∧ -n ≤ p.2.1 ∧ p.2.1 ≤ n ∧ -n ≤ p.2.2 ∧ p.2.2 ≤ n) := by
    intro p
    rw [hA, hB]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx, hy, hz⟩, heqn⟩
      rw [D8_eq_base_add_bump] at heqn
      by_cases hbump : p.1 = p.2.1 ∧ p.2.2 = 1 - p.1
      · right
        rw [ite_eq_left hbump] at heqn
        exact ⟨hbump.1, hbump.2, by omega, hx.1, hx.2, hy.1, hy.2, hz.1, hz.2⟩
      · left
        rw [ite_eq_right hbump] at heqn
        exact ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, hbump⟩
    · rintro (⟨⟨⟨hx, hy, hz⟩, heqb⟩, hbump⟩ | ⟨hxy, hz1, hbase, hx1, hx2, hy1, hy2, hz1', hz2⟩)
      · refine ⟨⟨hx, hy, hz⟩, ?_⟩
        rw [D8_eq_base_add_bump, ite_eq_right hbump]
        omega
      · refine ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1', hz2⟩⟩, ?_⟩
        rw [D8_eq_base_add_bump, ite_eq_left ⟨hxy, hz1⟩]
        omega
  set D := B.filter (fun p => p.1 = p.2.1 ∧ p.2.2 = 1 - p.1) with hD
  set C := (Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).filter
      (fun p => p.1 = p.2.1 ∧ p.2.2 = 1 - p.1 ∧ D8base p.1 p.2.1 p.2.2 = n - 2) with hC
  have hAeq : A = (B \ D) ∪ C := by
    ext p
    rw [Finset.mem_union, Finset.mem_sdiff, hD, hC]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    rw [key p]
    constructor
    · rintro (⟨hpb, hnb⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
      · left; exact ⟨hpb, fun hcon => hnb hcon.2⟩
      · right; exact ⟨⟨⟨h4, h5⟩, ⟨h6, h7⟩, h8, h9⟩, h1, h2, h3⟩
    · rintro (⟨hpb, hnd⟩ | ⟨⟨⟨h4, h5⟩, ⟨h6, h7⟩, h8, h9⟩, h1, h2, h3⟩)
      · left; exact ⟨hpb, fun hcon => hnd ⟨hpb, hcon⟩⟩
      · right; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hdisj : Disjoint (B \ D) C := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    rw [Finset.mem_sdiff, hD] at hp1
    simp only [Finset.mem_filter] at hp1
    rw [hC] at hp2
    simp only [Finset.mem_filter] at hp2
    exact hp1.2 ⟨hp1.1, hp2.2.1, hp2.2.2.1⟩
  have hDsub : D ⊆ B := Finset.filter_subset _ _
  have hDcard : D.card = 2 := by
    have hbij : D = (Finset.filter (fun t => D8base t t (1 - t) = n)
        (Finset.Icc (-n - 1) (n + 1))).image (fun t => (t, t, 1 - t)) := by
      rw [hD, hB]
      ext ⟨px, py, pz⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hz1', hz2⟩, heqb⟩, hxy, hz1⟩
        exact ⟨px, ⟨⟨by omega, by omega⟩, by rw [← hxy] at heqb; rw [← hz1]; exact heqb⟩,
          rfl, hxy, hz1.symm⟩
      · rintro ⟨t, ⟨⟨ht1, ht2⟩, heqt⟩, hpx, hpy, hpz⟩
        subst hpx; subst hpy; subst hpz
        have hline := D8base_line t
        rw [heqt] at hline
        have hn0 : 0 ≤ n := by rw [hn]; positivity
        exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩, heqt⟩, rfl, rfl⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    have hnval : n = ((2 * k + 1 : ℕ) : Int) := hn
    rw [hnval]
    exact lineAtLevel_card (((2 * k + 1 : ℕ) : Int) + 1) (2 * k + 1) (by omega) (by omega)
      (by omega)
  have hCcard : C.card = 2 := by
    have hbij : C = (Finset.filter (fun t => D8base t t (1 - t) = n - 2)
        (Finset.Icc (-n - 1) (n + 1))).image (fun t => (t, t, 1 - t)) := by
      rw [hC]
      ext ⟨px, py, pz⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hz1', hz2⟩, hxy, hz1, hbase⟩
        exact ⟨px, ⟨⟨by omega, by omega⟩, by rw [← hxy] at hbase; rw [← hz1]; exact hbase⟩,
          rfl, hxy, hz1.symm⟩
      · rintro ⟨t, ⟨⟨ht1, ht2⟩, heqt⟩, hpx, hpy, hpz⟩
        subst hpx; subst hpy; subst hpz
        have hline := D8base_line t
        rw [heqt] at hline
        have hn0 : 0 ≤ n := by rw [hn]; positivity
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, rfl, rfl, heqt⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    have hnval : n - 2 = ((2 * k - 1 : ℕ) : Int) := by rw [hn]; omega
    rw [hnval]
    exact lineAtLevel_card (n + 1) (2 * k - 1) (by rw [hn]; omega) (by omega) (by omega)
  have hAcard : A.card = (B \ D).card + C.card := by
    rw [hAeq, Finset.card_union_of_disjoint hdisj]
  have hBcard : D.card ≤ B.card := Finset.card_le_card hDsub
  rw [hAcard, Finset.card_sdiff_of_subset hDsub, hDcard, hCcard] at *
  omega

end CountOdd
end Bcs
