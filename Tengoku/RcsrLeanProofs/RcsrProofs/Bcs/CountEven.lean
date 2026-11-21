/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Metric
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.CountOdd
import Tengoku.Seed.Data.Int.Interval
import Tengoku.Seed.Data.Finset.Prod
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Even-parity level-set cardinalities of the bcs distance functions (part 2)

`D5, D6, D7` are always even, with the same closed form `6k²` at `n = 2k`,
`k ≥ 1`. `D1` is always even too, but carries the exceptional `+2` bump term
on the line `x = y ∧ y = -z ∧ x ≠ 0`, giving `6k²+2` for `k ≥ 2` (the case
`k = 1`, i.e. `n = 2`, is genuinely exceptional: the bump line's only point
at that radius is excluded by `x ≠ 0`).

## Strategy

`D5 x y z` factors as `2 * max(|s|, |u-1|, |v-1|)` for `s = x+y+z`,
`u = x-y+z`, `v = -x+y+z` (an `omega`-checkable algebraic identity, verified
first with `#eval`). This mirrors `D2`'s diagonalization in `CountOdd.lean`
exactly, just scaled by `2` and shifted by `0, 1, 1` instead of unshifted with
an implicit `/2`; the counting toolkit (`card_xyz_uvw`, ball-difference) is
reused with the same shape, adapted to even level values.

`D6`, `D7` diagonalize the same way (shifts `1,0,1` and `0,0,1`
respectively); no clean pointwise coordinate-permutation reduction to `D5`
was found (checked exhaustively over sign/permutation combinations), so each
is proved directly by the same diagonalization + ball-difference argument.

`D1` factors as `D1base + bump`, `D1base x y z = 2 * max(|s|,|u|,|v|)`
(shifts `0,0,0`), following the exact `D8`/`D8base` bump-correction pattern
from `CountOdd.lean`: on the bump line `x=y=t, z=-t`, `D1base` reduces to
`2|t|`, taking every even value `≥ 0` exactly twice for `t ≠ 0` (once each at
`t = ±t₀`) and the value `0` only at the excluded point `t = 0`. So the bump
correction is a clean `+2` at every positive even level except it vanishes at
`n = 0` (no exceptional point to promote there) and is exceptional at `n = 2`
(only `k - 1 = 0` has no line points below it to promote in).
-/

namespace Bcs
namespace CountEven

open Finset

/-! ## Parity: `D5, D6, D7, D1` are always even -/

/--
@isnad1 id=eq.0h3v.s4.aa8dbb8f3f31 from=translated src=- shape=44ba1afa vocab=27e82c44
-/
theorem D5_even (x y z : Int) : D5 x y z % 2 = 0 := by unfold D5; omega
/--
@isnad1 id=eq.0h3v.s4.bd350f87119a from=translated src=- shape=44ba1afa vocab=f1fa1386
-/
theorem D6_even (x y z : Int) : D6 x y z % 2 = 0 := by unfold D6; omega
/--
@isnad1 id=eq.0h3v.s4.4b918742cd72 from=translated src=- shape=44ba1afa vocab=8987d278
-/
theorem D7_even (x y z : Int) : D7 x y z % 2 = 0 := by unfold D7; omega
/--
@isnad1 id=eq.0h3v.s4.8e0beadcff73 from=translated src=- shape=44ba1afa vocab=302c25eb
-/
theorem D1_even (x y z : Int) : D1 x y z % 2 = 0 := by unfold D1; split <;> omega

/--
@isnad1 id=le.0h3v.s4.148f2ab805bd from=translated src=- shape=ac9c39a3 vocab=9f752c66
-/
theorem D5_nonneg (x y z : Int) : 0 ≤ D5 x y z := by unfold D5; omega
/--
@isnad1 id=le.0h3v.s4.c26e4cbc0b68 from=translated src=- shape=ac9c39a3 vocab=43cde791
-/
theorem D6_nonneg (x y z : Int) : 0 ≤ D6 x y z := by unfold D6; omega
/--
@isnad1 id=le.0h3v.s4.90b926f08776 from=translated src=- shape=ac9c39a3 vocab=ec17f8a5
-/
theorem D7_nonneg (x y z : Int) : 0 ≤ D7 x y z := by unfold D7; omega
/--
@isnad1 id=le.0h3v.s4.dcfb4ac4a917 from=translated src=- shape=ac9c39a3 vocab=f958ccac
-/
theorem D1_nonneg (x y z : Int) : 0 ≤ D1 x y z := by unfold D1; split <;> omega

/-- Cardinality of the level set `{(x,y,z) ∈ Icc(-n,n)³ : f x y z = n}`.-/
def levelCard (f : Int → Int → Int → Int) (n : Nat) : Nat :=
  ((Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
    (fun p => f p.1 p.2.1 p.2.2 = (n : Int))).card

/-! ## Odd `n`: all four level sets are empty -/

/--
@isnad1 id=eq.1h1v.s5.19d55fa66776 from=translated src=- shape=d39c40ff vocab=11aed5ac
-/
theorem levelCard_D5_odd (n : Nat) (hn : n % 2 = 1) : levelCard D5 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D5_even x y z
  intro heq; rw [heq] at h; omega

/--
@isnad1 id=eq.1h1v.s5.07273f5d02e6 from=translated src=- shape=d39c40ff vocab=52c64a55
-/
theorem levelCard_D6_odd (n : Nat) (hn : n % 2 = 1) : levelCard D6 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D6_even x y z
  intro heq; rw [heq] at h; omega

/--
@isnad1 id=eq.1h1v.s5.cd3c3e42eba8 from=translated src=- shape=d39c40ff vocab=97c7c795
-/
theorem levelCard_D7_odd (n : Nat) (hn : n % 2 = 1) : levelCard D7 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D7_even x y z
  intro heq; rw [heq] at h; omega

/--
@isnad1 id=eq.1h1v.s5.c7bc1a183a47 from=translated src=- shape=d39c40ff vocab=a800d979
-/
theorem levelCard_D1_odd (n : Nat) (hn : n % 2 = 1) : levelCard D1 n = 0 := by
  unfold levelCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ -
  have h := D1_even x y z
  intro heq; rw [heq] at h; omega

/-! ## Small cases by kernel computation -/

/--
@isnad1 id=eq.0h0v.s3.24be8adfe02f from=translated src=- shape=904d2e91 vocab=6bd7d8a2
-/
theorem levelCard_D1_0 : levelCard D1 0 = 1 := by decide +kernel
/--
@isnad1 id=eq.0h0v.s3.88e52154d6e8 from=translated src=- shape=904d2e91 vocab=6bd7d8a2
-/
theorem levelCard_D1_2 : levelCard D1 2 = 6 := by decide +kernel
/--
@isnad1 id=eq.0h0v.s3.b912fdbb9b9d from=translated src=- shape=904d2e91 vocab=c4f3f26a
-/
theorem levelCard_D5_2 : levelCard D5 2 = 6 := by decide +kernel

/-! ## Change-of-variables toolkit: `(x,y,z) ↦ (x+y+z, x-y+z, -x+y+z)`

Transfers a filtered count over the `(x,y,z)` box to a filtered count over an
`(s,u,v)` box carrying the same-parity constraint, given confinement of the
predicate to both boxes. Identical statement and proof to the copy in
`CountOdd.lean` (kept local here per the self-containment requirement). -/

/--
@isnad1 id=eq.2h3v.s10.b7bfee6030db from=translated src=- shape=884a428d vocab=5092be48
-/
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

/-! ## `D5`'s diagonalization: `D5 x y z = 2 * max(|s|,|u-1|,|v-1|)` -/

/-- `F5 n s u v` holds iff `2 * max(|s|,|u-1|,|v-1|) = n` (abs-free, matching
`D5`'s decomposition into the six affine forms `±2s, ±2(u-1), ±2(v-1)`).-/
def F5 (n s u v : Int) : Prop :=
  ((-n ≤ 2 * s ∧ 2 * s ≤ n) ∧ (-n ≤ 2 * (u - 1) ∧ 2 * (u - 1) ≤ n) ∧
      (-n ≤ 2 * (v - 1) ∧ 2 * (v - 1) ≤ n)) ∧
    (2 * s = n ∨ -(2 * s) = n ∨ 2 * (u - 1) = n ∨ -(2 * (u - 1)) = n ∨
      2 * (v - 1) = n ∨ -(2 * (v - 1)) = n)

instance (n s u v : Int) : Decidable (F5 n s u v) := by unfold F5; infer_instance

/--
@isnad1 id=iff.0h4v.s6.55c46c755b24 from=translated src=- shape=0fcba9cd vocab=5444dd89
-/
theorem D5_eq_F5 (x y z n : Int) : D5 x y z = n ↔ F5 n (x + y + z) (x - y + z) (-x + y + z) := by
  unfold D5 F5; omega

/--
@isnad1 id=eq.0h1v.s9.96c1e48642dd from=translated src=- shape=dd74c3c4 vocab=0cf43eb9
-/
theorem levelCard_D5_eq_uvw (n : ℕ) :
    levelCard D5 n =
      ((Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int)).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F5 (n : Int) q.1 q.2.1 q.2.2).card := by
  unfold levelCard
  have hfilt : (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter (fun p => D5 p.1 p.2.1 p.2.2 = (n : Int))
      = (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
        (fun p => F5 (n : Int) (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2)
          (-p.1 + p.2.1 + p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    exact D5_eq_F5 p.1 p.2.1 p.2.2 n
  rw [hfilt]
  apply card_xyz_uvw n (2 * n + 2) (F5 (n : Int))
  · intro x y z hF
    unfold F5 at hF
    simp only [mem_Icc]
    omega
  · intro s u v hF
    unfold F5 at hF
    simp only [mem_Icc]
    omega

/-! ## Ball-difference count for `F5`

`F5 (2k) s u v` says `|s| ≤ k`, `|u-1| ≤ k`, `|v-1| ≤ k` (all halved, since
`2s, 2(u-1), 2(v-1)` are even and compared against `2k`), with at least one
equality. As `k` increases by `1` the "all `≤ k`" ball grows by exactly the
"at least one `= k`" shell, so the `F5`-count at `2k` is the ball-difference
`ball k - ball (k-1)`. -/

/-- The "ball": same-parity triples in a box of radius `N` with
`|s| ≤ k`, `|u-1|, |v-1| ≤ k`.-/
def ballF5 (N : ℕ) (k : Int) : Finset (Int × Int × Int) :=
  ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
    (fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
      (-k ≤ q.1 ∧ q.1 ≤ k) ∧
      (1 - k ≤ q.2.1 ∧ q.2.1 ≤ k + 1) ∧
      (1 - k ≤ q.2.2 ∧ q.2.2 ≤ k + 1)))

/--
@isnad1 id=le.1h3v.s5.a36a55a49558 from=translated src=- shape=2322701c vocab=a77f2ef4
-/
theorem ballF5_mono (N : ℕ) {m n : Int} (h : m ≤ n) : ballF5 N m ⊆ ballF5 N n := by
  unfold ballF5
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨hbox, hpar, hs, hu, hv⟩ := hp
  exact ⟨hbox, hpar, by omega, by omega, by omega⟩

/-- Even-parity count in `Icc(-k,k)` (`k : ℕ`): `k+1` if `k` even, `k` if odd.
@isnad1 id=eq.0h1v.s6.5251b3053e08 from=translated src=- shape=b6a8a60d vocab=90b9b083
-/
theorem evenCount_symm (k : ℕ) :
    ((Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 0)).card
      = if k % 2 = 0 then k + 1 else k := by
  induction k with
  | zero => decide
  | succ m ih =>
    have hexp : (Finset.Icc (-((m : Int) + 1)) ((m : Int) + 1))
        = insert (-((m : Int) + 1))
          (insert ((m : Int) + 1) (Finset.Icc (-(m : Int)) (m : Int))) := by
      ext v; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    push_cast
    rw [hexp, Finset.filter_insert, Finset.filter_insert]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · have h1 : ¬ ((-((m : Int) + 1)) % 2 = 0) := by omega
      have h2 : ¬ (((m : Int) + 1) % 2 = 0) := by omega
      simp only [h1, h2, ite_false]
      rw [ih, ite_eq_left hm, ite_eq_right (by omega : ¬ (m + 1) % 2 = 0)]
    · have h1 : ((-((m : Int) + 1)) % 2 = 0) := by omega
      have h2 : (((m : Int) + 1) % 2 = 0) := by omega
      simp only [h1, h2, ite_true]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
      · rw [ih, ite_eq_right (by omega : ¬ m % 2 = 0), ite_eq_left (by omega : (m + 1) % 2 = 0)]
      · simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]; omega

/-- Odd-parity count in `Icc(-k,k)` (`k : ℕ`): `k` if `k` even, `k+1` if odd.
@isnad1 id=eq.0h1v.s6.eeab920b39be from=translated src=- shape=aa1bbc03 vocab=90b9b083
-/
theorem oddCount_symm (k : ℕ) :
    ((Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 1)).card
      = if k % 2 = 0 then k else k + 1 := by
  have htot : (Finset.Icc (-(k : Int)) (k : Int)).card = 2 * k + 1 := by
    rw [Int.card_Icc]; omega
  have hsplit : (Finset.Icc (-(k : Int)) (k : Int))
      = (Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 0) ∪
        (Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 1) := by
    ext v; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_filter]; omega
  have hdisj : Disjoint ((Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 0))
      ((Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 1)) := by
    rw [Finset.disjoint_filter]
    intro v _ hv0 hv1
    omega
  have := Finset.card_union_of_disjoint hdisj
  rw [← hsplit, htot, evenCount_symm] at this
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk] at this ⊢ <;> omega

/-- `Icc(1-k,k+1)` is the `+1`-shift of `Icc(-k,k)`, so its parity counts swap
relative to `evenCount_symm`/`oddCount_symm`.
@isnad1 id=eq.0h1v.s6.64e893fefa22 from=translated src=- shape=5d5f3f3e vocab=03a1940a
-/
theorem shift_iff (k : ℕ) :
    (Finset.Icc (1 - (k : Int)) ((k : Int) + 1))
      = (Finset.Icc (-(k : Int)) (k : Int)).image (fun v => v + 1) := by
  ext v
  simp only [Finset.mem_Icc, Finset.mem_image]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨v - 1, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩; omega

/--
@isnad1 id=eq.0h1v.s7.fadb864f59c3 from=translated src=- shape=127ffc4a vocab=9f9ab12a
-/
theorem evenCount_shift (k : ℕ) :
    ((Finset.Icc (1 - (k : Int)) ((k : Int) + 1)).filter (fun v => v % 2 = 0)).card
      = if k % 2 = 0 then k else k + 1 := by
  rw [shift_iff]
  have heq : (((Finset.Icc (-(k : Int)) (k : Int)).image (fun v => v + 1)).filter
        (fun v => v % 2 = 0))
      = ((Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 1)).image
        (fun v => v + 1) := by
    rw [Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hpar⟩; exact ⟨hv, by omega⟩
    · rintro ⟨hv, hpar⟩; exact ⟨hv, by omega⟩
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => by omega), oddCount_symm]

/--
@isnad1 id=eq.0h1v.s7.061d2ce46cdb from=translated src=- shape=3e81418c vocab=9f9ab12a
-/
theorem oddCount_shift (k : ℕ) :
    ((Finset.Icc (1 - (k : Int)) ((k : Int) + 1)).filter (fun v => v % 2 = 1)).card
      = if k % 2 = 0 then k + 1 else k := by
  rw [shift_iff]
  have heq : (((Finset.Icc (-(k : Int)) (k : Int)).image (fun v => v + 1)).filter
        (fun v => v % 2 = 1))
      = ((Finset.Icc (-(k : Int)) (k : Int)).filter (fun v => v % 2 = 0)).image
        (fun v => v + 1) := by
    rw [Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hpar⟩; exact ⟨hv, by omega⟩
    · rintro ⟨hv, hpar⟩; exact ⟨hv, by omega⟩
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => by omega), evenCount_symm]

set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.2h2v.s9.b95d7a86fbdf from=translated src=- shape=eb71a1ec vocab=e30b41f5
-/
theorem F5Card_eq_ball_diff (N : ℕ) (k : ℕ) (hk : 1 ≤ k) (_hN : k + 1 ≤ N) :
    ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F5 ((2 * k : ℕ) : Int) q.1 q.2.1 q.2.2).card
      = (ballF5 N (k : Int)).card - (ballF5 N ((k : Int) - 1)).card := by
  have hsub : ballF5 N ((k : Int) - 1) ⊆ ballF5 N (k : Int) := ballF5_mono N (by omega)
  have hcard_diff : (ballF5 N (k : Int)).card - (ballF5 N ((k : Int) - 1)).card
      = ((ballF5 N (k : Int)) \ (ballF5 N ((k : Int) - 1))).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  rw [hcard_diff]
  congr 1
  unfold ballF5
  ext ⟨a, b, c⟩
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  unfold F5
  constructor
  · rintro ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, hor⟩
    refine ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound1, hbound2, hbound3⟩, hnotin⟩
    refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_⟩
    · omega
    · by_contra hor
      push Not at hor
      apply hnotin
      refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩ <;> omega

/-! ## `D6`'s diagonalization: `D6 x y z = 2 * max(|s-1|,|u|,|v-1|)`

Same shape as `D5` with the shift moved from `s` to `u` (`D5` shifts `u,v`;
`D6` shifts `s,v`). No pointwise coordinate-permutation reduction to `D5` was
found (checked exhaustively over sign/permutation combinations), so `D6` is
proved directly by the same diagonalization + ball-difference argument, with
`s` and `u` swapping their roles (`s` now uses the shifted interval
`Icc(1-k,k+1)`, `u` uses the unshifted `Icc(-k,k)`). -/

/-- `F6 n s u v` holds iff `2 * max(|s-1|,|u|,|v-1|) = n`.-/
def F6 (n s u v : Int) : Prop :=
  ((-n ≤ 2 * (s - 1) ∧ 2 * (s - 1) ≤ n) ∧ (-n ≤ 2 * u ∧ 2 * u ≤ n) ∧
      (-n ≤ 2 * (v - 1) ∧ 2 * (v - 1) ≤ n)) ∧
    (2 * (s - 1) = n ∨ -(2 * (s - 1)) = n ∨ 2 * u = n ∨ -(2 * u) = n ∨
      2 * (v - 1) = n ∨ -(2 * (v - 1)) = n)

instance (n s u v : Int) : Decidable (F6 n s u v) := by unfold F6; infer_instance

/--
@isnad1 id=iff.0h4v.s6.adc2aafa1675 from=translated src=- shape=0fcba9cd vocab=aaab9032
-/
theorem D6_eq_F6 (x y z n : Int) : D6 x y z = n ↔ F6 n (x + y + z) (x - y + z) (-x + y + z) := by
  unfold D6 F6; omega

/--
@isnad1 id=eq.0h1v.s9.13e186b34010 from=translated src=- shape=dd74c3c4 vocab=38b063c7
-/
theorem levelCard_D6_eq_uvw (n : ℕ) :
    levelCard D6 n =
      ((Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int)).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F6 (n : Int) q.1 q.2.1 q.2.2).card := by
  unfold levelCard
  have hfilt : (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter (fun p => D6 p.1 p.2.1 p.2.2 = (n : Int))
      = (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
        (fun p => F6 (n : Int) (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2)
          (-p.1 + p.2.1 + p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    exact D6_eq_F6 p.1 p.2.1 p.2.2 n
  rw [hfilt]
  apply card_xyz_uvw n (2 * n + 2) (F6 (n : Int))
  · intro x y z hF
    unfold F6 at hF
    simp only [mem_Icc]
    omega
  · intro s u v hF
    unfold F6 at hF
    simp only [mem_Icc]
    omega

/-- The "ball" for `F6`: same-parity triples with `|s-1| ≤ k`, `|u| ≤ k`,
`|v-1| ≤ k`.-/
def ballF6 (N : ℕ) (k : Int) : Finset (Int × Int × Int) :=
  ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
    (fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
      (1 - k ≤ q.1 ∧ q.1 ≤ k + 1) ∧
      (-k ≤ q.2.1 ∧ q.2.1 ≤ k) ∧
      (1 - k ≤ q.2.2 ∧ q.2.2 ≤ k + 1)))

/--
@isnad1 id=le.1h3v.s5.e447d3875378 from=translated src=- shape=2322701c vocab=62da76fb
-/
theorem ballF6_mono (N : ℕ) {m n : Int} (h : m ≤ n) : ballF6 N m ⊆ ballF6 N n := by
  unfold ballF6
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨hbox, hpar, hs, hu, hv⟩ := hp
  exact ⟨hbox, hpar, by omega, by omega, by omega⟩

set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.2h2v.s9.29ef9d3b0c42 from=translated src=- shape=eb71a1ec vocab=d8efedf3
-/
theorem F6Card_eq_ball_diff (N : ℕ) (k : ℕ) (hk : 1 ≤ k) (_hN : k + 1 ≤ N) :
    ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F6 ((2 * k : ℕ) : Int) q.1 q.2.1 q.2.2).card
      = (ballF6 N (k : Int)).card - (ballF6 N ((k : Int) - 1)).card := by
  have hsub : ballF6 N ((k : Int) - 1) ⊆ ballF6 N (k : Int) := ballF6_mono N (by omega)
  have hcard_diff : (ballF6 N (k : Int)).card - (ballF6 N ((k : Int) - 1)).card
      = ((ballF6 N (k : Int)) \ (ballF6 N ((k : Int) - 1))).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  rw [hcard_diff]
  congr 1
  unfold ballF6
  ext ⟨a, b, c⟩
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  unfold F6
  constructor
  · rintro ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, hor⟩
    refine ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound1, hbound2, hbound3⟩, hnotin⟩
    refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_⟩
    · omega
    · by_contra hor
      push Not at hor
      apply hnotin
      refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩ <;> omega

/-! ## `D7`'s diagonalization: `D7 x y z = 2 * max(|s|,|u|,|v-1|)`

Same shape again, this time only `v` is shifted (`s`, `u` unshifted). No
pointwise coordinate-permutation reduction to `D5`/`D6` was found, so `D7` is
proved directly the same way. -/

/-- `F7 n s u v` holds iff `2 * max(|s|,|u|,|v-1|) = n`.-/
def F7 (n s u v : Int) : Prop :=
  ((-n ≤ 2 * s ∧ 2 * s ≤ n) ∧ (-n ≤ 2 * u ∧ 2 * u ≤ n) ∧
      (-n ≤ 2 * (v - 1) ∧ 2 * (v - 1) ≤ n)) ∧
    (2 * s = n ∨ -(2 * s) = n ∨ 2 * u = n ∨ -(2 * u) = n ∨
      2 * (v - 1) = n ∨ -(2 * (v - 1)) = n)

instance (n s u v : Int) : Decidable (F7 n s u v) := by unfold F7; infer_instance

/--
@isnad1 id=iff.0h4v.s6.b495c55fef9d from=translated src=- shape=0fcba9cd vocab=7e61a796
-/
theorem D7_eq_F7 (x y z n : Int) : D7 x y z = n ↔ F7 n (x + y + z) (x - y + z) (-x + y + z) := by
  unfold D7 F7; omega

/--
@isnad1 id=eq.0h1v.s9.8772e1c93099 from=translated src=- shape=dd74c3c4 vocab=74100708
-/
theorem levelCard_D7_eq_uvw (n : ℕ) :
    levelCard D7 n =
      ((Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int)).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F7 (n : Int) q.1 q.2.1 q.2.2).card := by
  unfold levelCard
  have hfilt : (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter (fun p => D7 p.1 p.2.1 p.2.2 = (n : Int))
      = (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
        (fun p => F7 (n : Int) (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2)
          (-p.1 + p.2.1 + p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    exact D7_eq_F7 p.1 p.2.1 p.2.2 n
  rw [hfilt]
  apply card_xyz_uvw n (2 * n + 2) (F7 (n : Int))
  · intro x y z hF
    unfold F7 at hF
    simp only [mem_Icc]
    omega
  · intro s u v hF
    unfold F7 at hF
    simp only [mem_Icc]
    omega

/-- The "ball" for `F7`: same-parity triples with `|s| ≤ k`, `|u| ≤ k`,
`|v-1| ≤ k`.-/
def ballF7 (N : ℕ) (k : Int) : Finset (Int × Int × Int) :=
  ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
    (fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
      (-k ≤ q.1 ∧ q.1 ≤ k) ∧
      (-k ≤ q.2.1 ∧ q.2.1 ≤ k) ∧
      (1 - k ≤ q.2.2 ∧ q.2.2 ≤ k + 1)))

/--
@isnad1 id=le.1h3v.s5.0caffa044a6d from=translated src=- shape=2322701c vocab=7835219f
-/
theorem ballF7_mono (N : ℕ) {m n : Int} (h : m ≤ n) : ballF7 N m ⊆ ballF7 N n := by
  unfold ballF7
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨hbox, hpar, hs, hu, hv⟩ := hp
  exact ⟨hbox, hpar, by omega, by omega, by omega⟩

set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.2h2v.s9.b4070d548f0d from=translated src=- shape=eb71a1ec vocab=97995e1f
-/
theorem F7Card_eq_ball_diff (N : ℕ) (k : ℕ) (hk : 1 ≤ k) (_hN : k + 1 ≤ N) :
    ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F7 ((2 * k : ℕ) : Int) q.1 q.2.1 q.2.2).card
      = (ballF7 N (k : Int)).card - (ballF7 N ((k : Int) - 1)).card := by
  have hsub : ballF7 N ((k : Int) - 1) ⊆ ballF7 N (k : Int) := ballF7_mono N (by omega)
  have hcard_diff : (ballF7 N (k : Int)).card - (ballF7 N ((k : Int) - 1)).card
      = ((ballF7 N (k : Int)) \ (ballF7 N ((k : Int) - 1))).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  rw [hcard_diff]
  congr 1
  unfold ballF7
  ext ⟨a, b, c⟩
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  unfold F7
  constructor
  · rintro ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, hor⟩
    refine ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound1, hbound2, hbound3⟩, hnotin⟩
    refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_⟩
    · omega
    · by_contra hor
      push Not at hor
      apply hnotin
      refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩ <;> omega

/-! ## `D1`: unbumped base, diagonalization, and the bump-line correction

`D1 x y z = D1base x y z + (2 if x = y ∧ y = -z ∧ x ≠ 0 else 0)`, where
`D1base` is the max of the same six affine forms as `D1` without the bump
term: `D1base x y z = 2 * max(|s|,|u|,|v|)` in the same
`(s,u,v) = (x+y+z, x-y+z, -x+y+z)` coordinates (an `omega`-checkable
identity, verified first with `#eval`) — unshifted, unlike `D5/D6/D7`.
Restricted to the bump line `x=y=t, z=-t`, `D1base` reduces to `2|t|` (an
exact computation: `s=t`, `u=v=-t`), which takes every positive even value
exactly twice (`t = ±m/2`) and the value `0` only at the excluded point
`t = 0` (`x ≠ 0` rules it out) — giving the exact bump correction: a net-zero
shift at every level `≥ 4`, and an uncompensated `-2` at level `2` (nothing
promotes in from level `0`, since the line's only level-`0` point is
excluded). -/

def D1base (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z) <| max (2*x - 2*y + 2*z) <| max (-2*x + 2*y + 2*z) <|
    max (-2*x - 2*y - 2*z) <| max (2*x - 2*y - 2*z) (-2*x + 2*y - 2*z)

/--
@isnad1 id=eq.0h3v.s6.4834223080e6 from=translated src=- shape=688cefa0 vocab=99fdb65a
-/
theorem D1_eq_base_add_bump (x y z : Int) :
    D1 x y z = D1base x y z + (if x = y ∧ y = -z ∧ x ≠ 0 then 2 else 0) := by
  unfold D1 D1base; rfl

/--
@isnad1 id=eq.0h3v.s4.f21ceec82060 from=translated src=- shape=44ba1afa vocab=a43b72d2
-/
theorem D1base_even (x y z : Int) : D1base x y z % 2 = 0 := by unfold D1base; omega
/--
@isnad1 id=le.0h3v.s4.6b271485c9e7 from=translated src=- shape=ac9c39a3 vocab=4f51c84a
-/
theorem D1base_nonneg (x y z : Int) : 0 ≤ D1base x y z := by unfold D1base; omega

/--
@isnad1 id=eq.0h1v.s4.3ed4e20a3da6 from=translated src=- shape=8a67f2aa vocab=050d4516
-/
theorem D1base_line (t : Int) : D1base t t (-t) = 2 * max t (-t) := by
  unfold D1base; omega

/-- `F1 n s u v` holds iff `2 * max(|s|,|u|,|v|) = n`.-/
def F1 (n s u v : Int) : Prop :=
  ((-n ≤ 2 * s ∧ 2 * s ≤ n) ∧ (-n ≤ 2 * u ∧ 2 * u ≤ n) ∧ (-n ≤ 2 * v ∧ 2 * v ≤ n)) ∧
    (2 * s = n ∨ -(2 * s) = n ∨ 2 * u = n ∨ -(2 * u) = n ∨ 2 * v = n ∨ -(2 * v) = n)

instance (n s u v : Int) : Decidable (F1 n s u v) := by unfold F1; infer_instance

/--
@isnad1 id=iff.0h4v.s6.079e42b6e21b from=translated src=- shape=0fcba9cd vocab=71424a6a
-/
theorem D1base_eq_F1 (x y z n : Int) :
    D1base x y z = n ↔ F1 n (x + y + z) (x - y + z) (-x + y + z) := by
  unfold D1base F1; omega

def levelCard1base (n : Nat) : Nat :=
  ((Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
    (fun p => D1base p.1 p.2.1 p.2.2 = (n : Int))).card

/--
@isnad1 id=eq.0h1v.s9.2b9f4750f8e4 from=translated src=- shape=282e89a6 vocab=1999ad35
-/
theorem levelCard1base_eq_uvw (n : ℕ) :
    levelCard1base n =
      ((Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int) ×ˢ
          Icc (-((2 * n + 2 : ℕ) : Int)) ((2 * n + 2 : ℕ) : Int)).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F1 (n : Int) q.1 q.2.1 q.2.2).card := by
  unfold levelCard1base
  have hfilt : (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter (fun p => D1base p.1 p.2.1 p.2.2 = (n : Int))
      = (Finset.Icc (-(n : Int)) (n : Int) ×ˢ Finset.Icc (-(n : Int)) (n : Int) ×ˢ
      Finset.Icc (-(n : Int)) (n : Int)).filter
        (fun p => F1 (n : Int) (p.1 + p.2.1 + p.2.2) (p.1 - p.2.1 + p.2.2)
          (-p.1 + p.2.1 + p.2.2)) := by
    apply Finset.filter_congr
    intro p _
    exact D1base_eq_F1 p.1 p.2.1 p.2.2 n
  rw [hfilt]
  apply card_xyz_uvw n (2 * n + 2) (F1 (n : Int))
  · intro x y z hF
    unfold F1 at hF
    simp only [mem_Icc]
    omega
  · intro s u v hF
    unfold F1 at hF
    simp only [mem_Icc]
    omega

/-- The "ball" for `F1`: same-parity triples with `|s| ≤ k`, `|u| ≤ k`,
`|v| ≤ k` (all three unshifted, unlike `F5/F6/F7`).-/
def ballF1 (N : ℕ) (k : Int) : Finset (Int × Int × Int) :=
  ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
    (fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
      (-k ≤ q.1 ∧ q.1 ≤ k) ∧
      (-k ≤ q.2.1 ∧ q.2.1 ≤ k) ∧
      (-k ≤ q.2.2 ∧ q.2.2 ≤ k)))

/--
@isnad1 id=le.1h3v.s5.91514c348468 from=translated src=- shape=2322701c vocab=8c2c0238
-/
theorem ballF1_mono (N : ℕ) {m n : Int} (h : m ≤ n) : ballF1 N m ⊆ ballF1 N n := by
  unfold ballF1
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨hbox, hpar, hs, hu, hv⟩ := hp
  exact ⟨hbox, hpar, by omega, by omega, by omega⟩

set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.2h2v.s9.c03b15336c7c from=translated src=- shape=eb71a1ec vocab=d2c25afa
-/
theorem F1Card_eq_ball_diff (N : ℕ) (k : ℕ) (hk : 1 ≤ k) (_hN : k + 1 ≤ N) :
    ((Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N ×ˢ Icc (-(N : Int)) N).filter
        fun q => (q.1 % 2 = q.2.1 % 2 ∧ q.2.1 % 2 = q.2.2 % 2) ∧
          F1 ((2 * k : ℕ) : Int) q.1 q.2.1 q.2.2).card
      = (ballF1 N (k : Int)).card - (ballF1 N ((k : Int) - 1)).card := by
  have hsub : ballF1 N ((k : Int) - 1) ⊆ ballF1 N (k : Int) := ballF1_mono N (by omega)
  have hcard_diff : (ballF1 N (k : Int)).card - (ballF1 N ((k : Int) - 1)).card
      = ((ballF1 N (k : Int)) \ (ballF1 N ((k : Int) - 1))).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  rw [hcard_diff]
  congr 1
  unfold ballF1
  ext ⟨a, b, c⟩
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  unfold F1
  constructor
  · rintro ⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound, hor⟩
    refine ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨⟨⟨hboxa, hboxb, hboxc⟩, hpar, hbound1, hbound2, hbound3⟩, hnotin⟩
    refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_⟩
    · omega
    · by_contra hor
      push Not at hor
      apply hnotin
      refine ⟨⟨hboxa, hboxb, hboxc⟩, hpar, ?_, ?_, ?_⟩ <;> omega

/--
@isnad1 id=eq.0h0v.s3.5bfdd98050d4 from=translated src=- shape=3c26ae4f vocab=5f78a347
-/
theorem levelCard1base_1 : levelCard1base 1 = 0 := by decide +kernel

/-- On the bump line, the number of points with `D1base = m` (`m` a *positive*
even) is exactly `2` (the two roots `t = ±m/2` of `2|t| = m`, both nonzero so
both are eligible for the bump). At `m = 0` the only line point is `t = 0`,
which the bump condition excludes (`x ≠ 0`), so it never counts as a bump
point at all — handled separately below.
@isnad1 id=eq.3h2v.s6.ceb93731478a from=translated src=- shape=4f15ff6a vocab=910f58db
-/
theorem lineAtLevel1_card (M : Int) (m : ℕ) (hM : (m : Int) + 1 ≤ M) (hm : 1 ≤ m)
    (hmeven : m % 2 = 0) :
    ((Finset.Icc (-M) M).filter (fun t => D1base t t (-t) = (m : Int))).card = 2 := by
  have heq : (Finset.Icc (-M) M).filter
      (fun t => D1base t t (-t) = (m : Int)) = {(m : Int) / 2, -((m : Int) / 2)} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      D1base_line]
    omega
  rw [heq]
  have hne : (m : Int) / 2 ≠ -((m : Int) / 2) := by omega
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

set_option maxHeartbeats 1000000 in
-- the bump-correction bijection argument needs the extra budget, same as `CountOdd`'s D8 analogue
/-- **The bump correction for `D1` at `n = 2k ≥ 4`**: for `k ≥ 2`, both `n` and
`n-2` are even and `≥ 2`, so the bump line contributes exactly `2` points
removed (bumped from level `n` to `n+2`) and `2` points added (bumped from
level `n-2` into level `n`) — a net-zero correction, so `D1` and `D1base` have
the same level-`n` cardinality.
@isnad1 id=eq.1h1v.s5.a37868542b23 from=translated src=- shape=2ba538c8 vocab=c886aa1d
-/
theorem levelCard_D1_eq_base (k : ℕ) (hk : 2 ≤ k) :
    levelCard D1 (2 * k) = levelCard1base (2 * k) := by
  unfold levelCard levelCard1base
  set n : Int := ((2 * k : ℕ) : Int) with hn
  set A := (Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).filter
      (fun p => D1 p.1 p.2.1 p.2.2 = n) with hA
  set B := (Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).filter
      (fun p => D1base p.1 p.2.1 p.2.2 = n) with hB
  have key : ∀ p : Int × Int × Int, p ∈ A ↔
      (p ∈ B ∧ ¬(p.1 = p.2.1 ∧ p.2.1 = -p.2.2 ∧ p.1 ≠ 0)) ∨
      (p.1 = p.2.1 ∧ p.2.1 = -p.2.2 ∧ p.1 ≠ 0 ∧ D1base p.1 p.2.1 p.2.2 = n - 2 ∧
        -n ≤ p.1 ∧ p.1 ≤ n ∧ -n ≤ p.2.1 ∧ p.2.1 ≤ n ∧ -n ≤ p.2.2 ∧ p.2.2 ≤ n) := by
    intro p
    rw [hA, hB]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx, hy, hz⟩, heqn⟩
      rw [D1_eq_base_add_bump] at heqn
      by_cases hbump : p.1 = p.2.1 ∧ p.2.1 = -p.2.2 ∧ p.1 ≠ 0
      · right
        rw [ite_eq_left hbump] at heqn
        exact ⟨hbump.1, hbump.2.1, hbump.2.2, by omega, hx.1, hx.2, hy.1, hy.2, hz.1, hz.2⟩
      · left
        rw [ite_eq_right hbump] at heqn
        exact ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, hbump⟩
    · rintro (⟨⟨⟨hx, hy, hz⟩, heqb⟩, hbump⟩ |
        ⟨hxy, hyz, hx0, hbase, hx1, hx2, hy1, hy2, hz1, hz2⟩)
      · refine ⟨⟨hx, hy, hz⟩, ?_⟩
        rw [D1_eq_base_add_bump, ite_eq_right hbump]
        omega
      · refine ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩, ?_⟩
        rw [D1_eq_base_add_bump, ite_eq_left ⟨hxy, hyz, hx0⟩]
        omega
  set D := B.filter (fun p => p.1 = p.2.1 ∧ p.2.1 = -p.2.2 ∧ p.1 ≠ 0) with hD
  set C := (Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).filter
      (fun p => p.1 = p.2.1 ∧ p.2.1 = -p.2.2 ∧ p.1 ≠ 0 ∧ D1base p.1 p.2.1 p.2.2 = n - 2) with hC
  have hAeq : A = (B \ D) ∪ C := by
    ext p
    rw [Finset.mem_union, Finset.mem_sdiff, hD, hC]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    rw [key p]
    constructor
    · rintro (⟨hpb, hnb⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩)
      · left; exact ⟨hpb, fun hcon => hnb hcon.2⟩
      · right; exact ⟨⟨⟨h5, h6⟩, ⟨h7, h8⟩, h9, h10⟩, h1, h2, h3, h4⟩
    · rintro (⟨hpb, hnd⟩ | ⟨⟨⟨h5, h6⟩, ⟨h7, h8⟩, h9, h10⟩, h1, h2, h3, h4⟩)
      · left; exact ⟨hpb, fun hcon => hnd ⟨hpb, hcon⟩⟩
      · right; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hdisj : Disjoint (B \ D) C := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    rw [Finset.mem_sdiff, hD] at hp1
    simp only [Finset.mem_filter] at hp1
    rw [hC] at hp2
    simp only [Finset.mem_filter] at hp2
    exact absurd ⟨hp1.1, hp2.2.1, hp2.2.2.1, hp2.2.2.2.1⟩ hp1.2
  have hDsub : D ⊆ B := Finset.filter_subset _ _
  have hDcard : D.card = 2 := by
    have hbij : D = (Finset.filter (fun t => D1base t t (-t) = n)
        (Finset.Icc (-(n + 1)) (n + 1))).image (fun t => (t, t, -t)) := by
      rw [hD, hB]
      ext ⟨px, py, pz⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hz1', hz2⟩, heqb⟩, hxy, hyz, hx0⟩
        refine ⟨px, ⟨⟨by omega, by omega⟩, ?_⟩, rfl, by omega, by omega⟩
        have hpz : pz = -px := by omega
        rw [show py = px from hxy.symm, hpz] at heqb
        exact heqb
      · rintro ⟨t, ⟨⟨ht1, ht2⟩, heqt⟩, hpx, hpy, hpz⟩
        subst hpx; subst hpy; subst hpz
        have hn0 : 0 ≤ n := by rw [hn]; positivity
        have hline := D1base_line t
        rw [heqt] at hline
        have ht0 : t ≠ 0 := by
          intro hteq; subst hteq
          rw [D1base_line] at heqt
          simp only [neg_zero, max_self] at heqt
          omega
        exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩, heqt⟩,
          rfl, by omega, ht0⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    have hnval : n = ((2 * k : ℕ) : Int) := hn
    rw [hnval]
    exact lineAtLevel1_card (((2 * k : ℕ) : Int) + 1) (2 * k) (by omega) (by omega) (by omega)
  have hCcard : C.card = 2 := by
    have hbij : C = (Finset.filter (fun t => D1base t t (-t) = n - 2)
        (Finset.Icc (-(n + 1)) (n + 1))).image (fun t => (t, t, -t)) := by
      rw [hC]
      ext ⟨px, py, pz⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hz1', hz2⟩, hxy, hyz, hx0, hbase⟩
        refine ⟨px, ⟨⟨by omega, by omega⟩, ?_⟩, rfl, by omega, by omega⟩
        have hpz : pz = -px := by omega
        rw [show py = px from hxy.symm, hpz] at hbase
        exact hbase
      · rintro ⟨t, ⟨⟨ht1, ht2⟩, heqt⟩, hpx, hpy, hpz⟩
        subst hpx; subst hpy; subst hpz
        have hline := D1base_line t
        rw [heqt] at hline
        have ht0 : t ≠ 0 := by
          intro hteq; subst hteq
          rw [D1base_line] at heqt
          simp only [neg_zero, max_self] at heqt
          omega
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, rfl, by omega, ht0, heqt⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    have hnval : n - 2 = ((2 * (k - 1) : ℕ) : Int) := by rw [hn]; omega
    rw [hnval]
    exact lineAtLevel1_card (n + 1) (2 * (k - 1)) (by rw [hn]; omega) (by omega) (by omega)
  have hAcard : A.card = (B \ D).card + C.card := by
    rw [hAeq, Finset.card_union_of_disjoint hdisj]
  have hBcard : D.card ≤ B.card := Finset.card_le_card hDsub
  rw [hAcard, Finset.card_sdiff_of_subset hDsub, hDcard, hCcard] at *
  omega

end CountEven
end Bcs
