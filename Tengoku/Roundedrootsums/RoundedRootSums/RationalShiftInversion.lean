/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact inversion for rational shifts

This file connects the rational-shift double-counting infrastructure
with rounded reciprocal-root sums and proves the exact inversion formula.
-/

namespace RoundedRootSums

/--
The number of shifted threshold levels among `1, ..., t`
that are reached by `k`.-/
def shiftedRoundedValueUpTo
    (q a b k t : Nat) : Nat :=
  shiftedLevelCount q a b k t

/--
The truncated rationally shifted reciprocal-root sum,
with levels restricted to `1, ..., t`.-/
def shiftedRoundedSumUpTo
    (q a b n t : Nat) : Nat :=
  Finset.sum (Finset.Icc 1 n) (fun k =>
    shiftedRoundedValueUpTo q a b k t)

/--
The truncated shifted rounded sum is exactly the level-count sum.
@isnad1 id=eq.0h5v.s4.c6325ac2d79e from=translated src=- shape=37b02ddb vocab=1ee9462c
-/
theorem shiftedRoundedSumUpTo_eq_levelCountSum
    (q a b n t : Nat) :
    shiftedRoundedSumUpTo q a b n t =
      shiftedLevelCountSum q a b n t := by
  rfl

/--
Exact inversion for the truncated rationally shifted sum.
@isnad1 id=eq.2h5v.s5.da386a8bec41 from=translated src=- shape=a88f716c vocab=76756fd3
-/
theorem shiftedRoundedSumUpTo_eq_inversionSum
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedSumUpTo q a b n t =
      shiftedInversionSum q a b n t := by
  calc
    shiftedRoundedSumUpTo q a b n t =
        shiftedLevelCountSum q a b n t :=
      shiftedRoundedSumUpTo_eq_levelCountSum q a b n t
    _ = shiftedInversionSum q a b n t :=
      shiftedLevelCountSum_eq_inversionSum q a b n t hb ha

/--
The canonical finite shifted rounded value for `k`,
using the common level bound `n + 1`.-/
def shiftedRoundedValueBounded
    (q a b n k : Nat) : Nat :=
  shiftedRoundedValueUpTo q a b k (n + 1)

/--
The canonical finite rationally shifted rounded sum.-/
def shiftedRoundedSumBounded
    (q a b n : Nat) : Nat :=
  Finset.sum (Finset.Icc 1 n) (fun k =>
    shiftedRoundedValueBounded q a b n k)

/--
The canonical bounded shifted sum is the truncated sum
with common level bound `n + 1`.
@isnad1 id=eq.0h4v.s5.e49a0fd51499 from=translated src=- shape=27653418 vocab=3ac9bf1e
-/
theorem shiftedRoundedSumBounded_eq_upTo
    (q a b n : Nat) :
    shiftedRoundedSumBounded q a b n =
      shiftedRoundedSumUpTo q a b n (n + 1) := by
  rfl

/--
Exact inversion for the canonical bounded shifted sum.
@isnad1 id=eq.2h4v.s5.2774848bc90d from=translated src=- shape=657e16c0 vocab=405bee74
-/
theorem shiftedRoundedSumBounded_eq_inversionSum
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedSumBounded q a b n =
      shiftedInversionSum q a b n (n + 1) := by
  calc
    shiftedRoundedSumBounded q a b n =
        shiftedRoundedSumUpTo q a b n (n + 1) :=
      shiftedRoundedSumBounded_eq_upTo q a b n
    _ = shiftedInversionSum q a b n (n + 1) :=
      shiftedRoundedSumUpTo_eq_inversionSum
        q a b n (n + 1) hb ha

/--
The shifted level count can be written directly using the
underlying rational-power inequality.
@isnad1 id=eq.2h5v.s7.32bf3a86792a from=translated src=- shape=3ef28c06 vocab=9fa65dae
-/
theorem shiftedLevelCount_eq_powerCount
    (q a b k t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedLevelCount q a b k t =
      ((Finset.range t).filter (fun m =>
        ((((m + 1 : Nat) : Rat) -
            (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat))).card := by
  have ham :
      ∀ m : Nat, a ≤ b * (m + 1) := by
    intro m
    calc
      a ≤ b := Nat.le_of_lt ha
      _ = b * 1 := by simp
      _ ≤ b * (m + 1) :=
        Nat.mul_le_mul_left b
          (Nat.succ_le_succ (Nat.zero_le m))
  unfold shiftedLevelCount
  refine congrArg Finset.card ?_
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨h.1,
      (shiftedThresholdNat_le_iff
        q a b (m + 1) k hb (ham m)).mp h.2⟩
  · intro h
    exact ⟨h.1,
      (shiftedThresholdNat_le_iff
        q a b (m + 1) k hb (ham m)).mpr h.2⟩

/--
The truncated shifted rounded value counts exactly the levels
whose shifted rational powers do not exceed `k`.
@isnad1 id=eq.2h5v.s7.b3e1d599e63e from=translated src=- shape=3ef28c06 vocab=fc215dc7
-/
theorem shiftedRoundedValueUpTo_eq_powerCount
    (q a b k t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedValueUpTo q a b k t =
      ((Finset.range t).filter (fun m =>
        ((((m + 1 : Nat) : Rat) -
            (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat))).card := by
  unfold shiftedRoundedValueUpTo
  exact shiftedLevelCount_eq_powerCount
    q a b k t hb ha

/--
The number of shifted rational-power levels among `1, ..., t`
whose q-th powers do not exceed `k`.-/
def shiftedPowerCount
    (q a b k t : Nat) : Nat :=
  ((Finset.range t).filter (fun m =>
    ((((m + 1 : Nat) : Rat) -
        (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat))).card

/--
The truncated shifted rounded value agrees with the direct
rational-power count.
@isnad1 id=eq.2h5v.s5.938a946a4c78 from=translated src=- shape=a88f716c vocab=2b7011e7
-/
theorem shiftedRoundedValueUpTo_eq_shiftedPowerCount
    (q a b k t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedValueUpTo q a b k t =
      shiftedPowerCount q a b k t := by
  unfold shiftedPowerCount
  exact shiftedRoundedValueUpTo_eq_powerCount
    q a b k t hb ha

/--
The sum of the direct rational-power counts over `k = 1, ..., n`.-/
def shiftedPowerCountSum
    (q a b n t : Nat) : Nat :=
  Finset.sum (Finset.Icc 1 n) (fun k =>
    shiftedPowerCount q a b k t)

/--
The truncated shifted rounded sum agrees with the sum
of the direct rational-power counts.
@isnad1 id=eq.2h5v.s5.3e5a760fc0f1 from=translated src=- shape=a88f716c vocab=4f181d17
-/
theorem shiftedRoundedSumUpTo_eq_shiftedPowerCountSum
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedSumUpTo q a b n t =
      shiftedPowerCountSum q a b n t := by
  unfold shiftedRoundedSumUpTo shiftedPowerCountSum
  apply Finset.sum_congr rfl
  intro k _hk
  exact shiftedRoundedValueUpTo_eq_shiftedPowerCount
    q a b k t hb ha

/--
The direct rational-power count sum satisfies the same
exact inversion formula.
@isnad1 id=eq.2h5v.s5.fd74a9178b13 from=translated src=- shape=a88f716c vocab=818b1055
-/
theorem shiftedPowerCountSum_eq_inversionSum
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedPowerCountSum q a b n t =
      shiftedInversionSum q a b n t := by
  calc
    shiftedPowerCountSum q a b n t =
        shiftedRoundedSumUpTo q a b n t :=
      (shiftedRoundedSumUpTo_eq_shiftedPowerCountSum
        q a b n t hb ha).symm
    _ = shiftedInversionSum q a b n t :=
      shiftedRoundedSumUpTo_eq_inversionSum
        q a b n t hb ha

/--
The canonical direct rational-power sum, using the common
level bound `n + 1`.-/
def shiftedPowerRoundedSum
    (q a b n : Nat) : Nat :=
  shiftedPowerCountSum q a b n (n + 1)

/--
Exact inversion for the canonical direct rational-power sum.
@isnad1 id=eq.2h4v.s5.424b84632168 from=translated src=- shape=657e16c0 vocab=453082d9
-/
theorem shiftedPowerRoundedSum_eq_inversionSum
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedPowerRoundedSum q a b n =
      shiftedInversionSum q a b n (n + 1) := by
  unfold shiftedPowerRoundedSum
  exact shiftedPowerCountSum_eq_inversionSum
    q a b n (n + 1) hb ha

/--
The largest number of shifted rational-power levels reached at `n`,
using the common finite bound `n + 1`.-/
def shiftedMaxLevel
    (q a b n : Nat) : Nat :=
  shiftedPowerCount q a b n (n + 1)

/--
The shifted power count is monotone in its upper value `k`.
@isnad1 id=le.1h6v.s5.f5ce1bc3a2b4 from=translated src=- shape=791091f2 vocab=a7d36cdd
-/
theorem shiftedPowerCount_mono
    (q a b k₁ k₂ t : Nat)
    (hk : k₁ ≤ k₂) :
    shiftedPowerCount q a b k₁ t ≤
      shiftedPowerCount q a b k₂ t := by
  have hkRat : (k₁ : Rat) ≤ (k₂ : Rat) := by
    exact_mod_cast hk
  unfold shiftedPowerCount
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
  exact ⟨hm.1, le_trans hm.2 hkRat⟩

/--
Every `k ≤ n` reaches at most `shiftedMaxLevel q a b n` levels.
@isnad1 id=le.1h5v.s5.90aba705a168 from=translated src=- shape=5769c1d0 vocab=31a612c4
-/
theorem shiftedPowerCount_le_maxLevel
    (q a b n k : Nat)
    (hk : k ≤ n) :
    shiftedPowerCount q a b k (n + 1) ≤
      shiftedMaxLevel q a b n := by
  unfold shiftedMaxLevel
  exact shiftedPowerCount_mono
    q a b k n (n + 1) hk

/--
The shifted rational base is nonnegative under the standard
assumptions `0 ≤ a < b`.
@isnad1 id=le.2h3v.s6.f1795de8f29e from=translated src=- shape=babd756b vocab=1697c5be
-/
theorem shiftedBase_nonneg
    (a b m : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    (0 : Rat) ≤
      ((m + 1 : Nat) : Rat) -
        (a : Rat) / (b : Rat) := by
  have hbRat : (0 : Rat) < (b : Rat) := by
    exact_mod_cast hb
  have haRat : (a : Rat) < (b : Rat) := by
    exact_mod_cast ha
  have hdiv :
      (a : Rat) / (b : Rat) < 1 := by
    exact (div_lt_one hbRat).2 haRat
  have hm :
      (1 : Rat) ≤ ((m + 1 : Nat) : Rat) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  linarith

/--
The shifted q-th power is monotone in the level index.
@isnad1 id=le.3h5v.s7.cd8c544094c9 from=translated src=- shape=38034a76 vocab=f3c7c7a5
-/
theorem shiftedPower_mono_level
    (q a b m₁ m₂ : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hm : m₁ ≤ m₂) :
    ((((m₁ + 1 : Nat) : Rat) -
        (a : Rat) / (b : Rat)) ^ q) ≤
      ((((m₂ + 1 : Nat) : Rat) -
        (a : Rat) / (b : Rat)) ^ q) := by
  have hmRat :
      ((m₁ + 1 : Nat) : Rat) ≤
        ((m₂ + 1 : Nat) : Rat) := by
    exact_mod_cast Nat.succ_le_succ hm
  have hbase :
      ((m₁ + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat) ≤
        ((m₂ + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat) := by
    exact sub_le_sub_right hmRat _
  exact pow_le_pow_left₀
    (shiftedBase_nonneg a b m₁ hb ha)
    hbase q

/--
If a level is reached, then every smaller level is reached as well.
@isnad1 id=le.4h6v.s7.3619e3d357c1 from=translated src=- shape=54261954 vocab=f3c7c7a5
-/
theorem shiftedPower_reached_downward
    (q a b k m₁ m₂ : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hm : m₁ ≤ m₂)
    (hreached :
      ((((m₂ + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat)) :
    ((((m₁ + 1 : Nat) : Rat) -
        (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat) := by
  exact le_trans
    (shiftedPower_mono_level
      q a b m₁ m₂ hb ha hm)
    hreached

/--
`IsShiftedCutoff q a b n t` means that `t` is the exact number
of shifted rational-power levels reached at `n`.

Precisely, among the candidate levels `0, ..., n`,
a level `m` is reached at `n` exactly when `m < t`.-/
def IsShiftedCutoff
    (q a b n t : Nat) : Prop :=
  t ≤ n + 1 ∧
    ∀ m : Nat, m < n + 1 →
      (((((m + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat) ↔
        m < t)

/--
If `t` is an exact cutoff at `n`, then for every `k ≤ n`
all reached levels already lie below `t`.
@isnad1 id=eq.2h6v.s5.b3f4ab5b3db3 from=translated src=- shape=54199124 vocab=15033160
-/
theorem shiftedPowerCount_eq_of_cutoff
    (q a b n k t : Nat)
    (hk : k ≤ n)
    (hcut : IsShiftedCutoff q a b n t) :
    shiftedPowerCount q a b k (n + 1) =
      shiftedPowerCount q a b k t := by
  rcases hcut with ⟨htn, hcut⟩
  unfold shiftedPowerCount
  apply congrArg Finset.card
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hm
    have hkRat : (k : Rat) ≤ (n : Rat) := by
      exact_mod_cast hk
    have hreachedN :
        ((((m + 1 : Nat) : Rat) -
            (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat) :=
      le_trans hm.2 hkRat
    have hmt : m < t :=
      (hcut m hm.1).mp hreachedN
    exact ⟨hmt, hm.2⟩
  · intro hm
    exact ⟨lt_of_lt_of_le hm.1 htn, hm.2⟩

/--
Exact inversion with an arbitrary exact cutoff `t`.

Once `t` is known to be the precise largest reached level,
the artificial common bound `n + 1` can be replaced by `t`.
@isnad1 id=eq.3h5v.s5.7f4fdd5de599 from=translated src=- shape=63827978 vocab=4a65ce36
-/
theorem shiftedPowerRoundedSum_eq_inversionSum_of_cutoff
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hcut : IsShiftedCutoff q a b n t) :
    shiftedPowerRoundedSum q a b n =
      shiftedInversionSum q a b n t := by
  calc
    shiftedPowerRoundedSum q a b n =
        shiftedPowerCountSum q a b n t := by
      unfold shiftedPowerRoundedSum shiftedPowerCountSum
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n :=
        (Finset.mem_Icc.mp hk).2
      exact shiftedPowerCount_eq_of_cutoff
        q a b n k t hkn hcut
    _ = shiftedInversionSum q a b n t :=
      shiftedPowerCountSum_eq_inversionSum
        q a b n t hb ha

/--
Among the candidate levels `0, ..., n`, a level `m` is reached
at `n` exactly when it lies below `shiftedMaxLevel`.
@isnad1 id=iff.3h5v.s6.c4e40619fb15 from=translated src=- shape=d0af131a vocab=3293bc36
-/
theorem shiftedPower_reached_iff_lt_maxLevel
    (q a b n m : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hmn : m < n + 1) :
    (((((m + 1 : Nat) : Rat) -
        (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat)) ↔
      m < shiftedMaxLevel q a b n := by
  constructor
  · intro hmreach
    have hsubset :
        Finset.range (m + 1) ⊆
          (Finset.range (n + 1)).filter (fun j =>
            (((((j + 1 : Nat) : Rat) -
                (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat))) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      have hjm : j ≤ m :=
        Nat.lt_succ_iff.mp hj
      have hjn : j < n + 1 :=
        lt_of_le_of_lt hjm hmn
      have hjreach :
          (((((j + 1 : Nat) : Rat) -
              (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat)) :=
        shiftedPower_reached_downward
          q a b n j m hb ha hjm hmreach
      exact ⟨hjn, hjreach⟩
    have hcard :=
      Finset.card_le_card hsubset
    have hsucc :
        m + 1 ≤ shiftedMaxLevel q a b n := by
      simpa [shiftedMaxLevel, shiftedPowerCount] using hcard
    exact Nat.lt_of_succ_le hsucc
  · intro hmmax
    by_contra hmreach
    have hsubset :
        (Finset.range (n + 1)).filter (fun j =>
            (((((j + 1 : Nat) : Rat) -
                (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat))) ⊆
          Finset.range m := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_range]
      by_contra hjm
      have hmj : m ≤ j :=
        Nat.le_of_not_gt hjm
      apply hmreach
      exact shiftedPower_reached_downward
        q a b n m j hb ha hmj hj.2
    have hcard :=
      Finset.card_le_card hsubset
    have hle :
        shiftedMaxLevel q a b n ≤ m := by
      simpa [shiftedMaxLevel, shiftedPowerCount] using hcard
    exact (Nat.not_lt_of_ge hle) hmmax

/--
`shiftedMaxLevel q a b n` is the exact cutoff for the shifted
rational-power levels reached at `n`.
@isnad1 id=isshifte.2h4v.s5.52c8325cabaf from=translated src=- shape=f4cfb39c vocab=8c35d7ac
-/
theorem shiftedMaxLevel_isCutoff
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    IsShiftedCutoff
      q a b n (shiftedMaxLevel q a b n) := by
  constructor
  · have hsubset :
        (Finset.range (n + 1)).filter (fun m =>
            (((((m + 1 : Nat) : Rat) -
                (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat))) ⊆
          Finset.range (n + 1) :=
      Finset.filter_subset _ _
    have hcard :=
      Finset.card_le_card hsubset
    simpa [shiftedMaxLevel, shiftedPowerCount] using hcard
  · intro m hm
    exact shiftedPower_reached_iff_lt_maxLevel
      q a b n m hb ha hm

/--
Exact inversion with the natural cutoff `shiftedMaxLevel`.
@isnad1 id=eq.2h4v.s5.1bf8890ad372 from=translated src=- shape=89f3ae4b vocab=a9b06873
-/
theorem shiftedPowerRoundedSum_eq_inversionSum_maxLevel
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedPowerRoundedSum q a b n =
      shiftedInversionSum q a b n
        (shiftedMaxLevel q a b n) := by
  exact shiftedPowerRoundedSum_eq_inversionSum_of_cutoff
    q a b n (shiftedMaxLevel q a b n) hb ha
      (shiftedMaxLevel_isCutoff q a b n hb ha)

/--
The bounded level-count model agrees with the direct
rational-power model.
@isnad1 id=eq.2h4v.s5.48e538a86f58 from=translated src=- shape=11bff3f4 vocab=a53dd911
-/
theorem shiftedRoundedSumBounded_eq_powerRoundedSum
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedSumBounded q a b n =
      shiftedPowerRoundedSum q a b n := by
  calc
    shiftedRoundedSumBounded q a b n =
        shiftedRoundedSumUpTo q a b n (n + 1) :=
      shiftedRoundedSumBounded_eq_upTo q a b n
    _ = shiftedPowerCountSum q a b n (n + 1) :=
      shiftedRoundedSumUpTo_eq_shiftedPowerCountSum
        q a b n (n + 1) hb ha
    _ = shiftedPowerRoundedSum q a b n := by
      rfl

/--
Exact inversion for the bounded shifted rounded sum,
with its natural maximal level.
@isnad1 id=eq.2h4v.s5.e43ae6d7be55 from=translated src=- shape=89f3ae4b vocab=43eb0fa7
-/
theorem shiftedRoundedSumBounded_eq_inversionSum_maxLevel
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRoundedSumBounded q a b n =
      shiftedInversionSum q a b n
        (shiftedMaxLevel q a b n) := by
  calc
    shiftedRoundedSumBounded q a b n =
        shiftedPowerRoundedSum q a b n :=
      shiftedRoundedSumBounded_eq_powerRoundedSum
        q a b n hb ha
    _ = shiftedInversionSum q a b n
          (shiftedMaxLevel q a b n) :=
      shiftedPowerRoundedSum_eq_inversionSum_maxLevel
        q a b n hb ha

/--
The sum of the natural shifted thresholds for levels `1, ..., t`.-/
def shiftedThresholdSum
    (q a b t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedThresholdNat q a b (m + 1))

/--
Every level below an exact cutoff has threshold at most `n`.
@isnad1 id=le.4h6v.s5.84e6fa2e2a79 from=translated src=- shape=47de92ed vocab=bf45a7f6
-/
theorem shiftedThresholdNat_le_n_of_lt_cutoff
    (q a b n t m : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hm : m < t)
    (hcut : IsShiftedCutoff q a b n t) :
    shiftedThresholdNat q a b (m + 1) ≤ n := by
  rcases hcut with ⟨htn, hlevels⟩
  have hmn : m < n + 1 :=
    lt_of_lt_of_le hm htn
  have hpow :
      (((((m + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat)) ^ q) ≤ (n : Rat)) :=
    (hlevels m hmn).mpr hm
  have ham : a ≤ b * (m + 1) := by
    calc
      a ≤ b := Nat.le_of_lt ha
      _ = b * 1 := by simp
      _ ≤ b * (m + 1) :=
        Nat.mul_le_mul_left b
          (Nat.succ_le_succ (Nat.zero_le m))
  exact
    (shiftedThresholdNat_le_iff
      q a b (m + 1) n hb ham).mpr hpow

/--
The inversion sum and the threshold sum add up to `t * (n + 1)`.
@isnad1 id=eq.3h5v.s6.66e1ce41d569 from=translated src=- shape=9d6ae557 vocab=c0395185
-/
theorem shiftedInversionSum_add_thresholdSum_of_cutoff
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hcut : IsShiftedCutoff q a b n t) :
    shiftedInversionSum q a b n t +
        shiftedThresholdSum q a b t =
      t * (n + 1) := by
  unfold shiftedInversionSum shiftedThresholdSum
  calc
    Finset.sum (Finset.range t) (fun m =>
        n + 1 - shiftedThresholdNat q a b (m + 1)) +
      Finset.sum (Finset.range t) (fun m =>
        shiftedThresholdNat q a b (m + 1))
        =
      Finset.sum (Finset.range t) (fun m =>
        (n + 1 - shiftedThresholdNat q a b (m + 1)) +
          shiftedThresholdNat q a b (m + 1)) := by
      symm
      exact Finset.sum_add_distrib
    _ = Finset.sum (Finset.range t) (fun _ => n + 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Nat.sub_add_cancel
      exact le_trans
        (shiftedThresholdNat_le_n_of_lt_cutoff
          q a b n t m hb ha
            (Finset.mem_range.mp hm) hcut)
        (Nat.le_succ n)
    _ = t * (n + 1) := by
      simp

/--
The inversion sum has the explicit form used in the article.
@isnad1 id=eq.3h5v.s6.ae0de8a9947f from=translated src=- shape=8eb224b4 vocab=c79c7971
-/
theorem shiftedInversionSum_eq_mul_sub_thresholdSum_of_cutoff
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hcut : IsShiftedCutoff q a b n t) :
    shiftedInversionSum q a b n t =
      t * (n + 1) - shiftedThresholdSum q a b t := by
  have h :=
    shiftedInversionSum_add_thresholdSum_of_cutoff
      q a b n t hb ha hcut
  omega

/--
The inversion sum at its natural cutoff has the explicit
product-minus-threshold-sum form used in the article.
@isnad1 id=eq.2h4v.s6.a8964b1877e8 from=translated src=- shape=5a172747 vocab=996d9ab7
-/
theorem shiftedInversionSum_eq_mul_sub_thresholdSum_maxLevel
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedInversionSum q a b n
        (shiftedMaxLevel q a b n) =
      shiftedMaxLevel q a b n * (n + 1) -
        shiftedThresholdSum q a b
          (shiftedMaxLevel q a b n) := by
  exact shiftedInversionSum_eq_mul_sub_thresholdSum_of_cutoff
    q a b n (shiftedMaxLevel q a b n) hb ha
      (shiftedMaxLevel_isCutoff q a b n hb ha)

/--
Exact inversion for the rationally shifted power-count sum,
in the explicit form used in the article.
@isnad1 id=eq.2h4v.s6.81587ea2a8c1 from=translated src=- shape=0c403d47 vocab=e807234b
-/
theorem shiftedPowerRoundedSum_explicit_formula
    (q a b n : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedPowerRoundedSum q a b n =
      shiftedMaxLevel q a b n * (n + 1) -
        shiftedThresholdSum q a b
          (shiftedMaxLevel q a b n) := by
  calc
    shiftedPowerRoundedSum q a b n =
        shiftedInversionSum q a b n
          (shiftedMaxLevel q a b n) :=
      shiftedPowerRoundedSum_eq_inversionSum_maxLevel
        q a b n hb ha
    _ = shiftedMaxLevel q a b n * (n + 1) -
          shiftedThresholdSum q a b
            (shiftedMaxLevel q a b n) :=
      shiftedInversionSum_eq_mul_sub_thresholdSum_maxLevel
        q a b n hb ha

end RoundedRootSums
