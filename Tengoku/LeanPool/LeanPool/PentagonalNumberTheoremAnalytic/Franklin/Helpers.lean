/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Defs

/-!
# Helper lemmas for Franklin's involution

Helper lemmas about `consecutiveTopRun`, partition membership,
and properties of `αOp`/`βOp`.

## Main results

* `ctr_zero`, `ctr_succ`: defining equations for `consecutiveTopRun`
* `ctr_eq_of`: the characterisation of `consecutiveTopRun S m` as the unique `r` with
  `m - j ∈ S` for all `j < r` and `m - r ∉ S`
* `mem_DP`: membership in `distinctPartitions`
* `sum_Icc_id_mul_two`, `Icc_sum_id`: Gauss' summation formula over `Finset.Icc` in `ℕ`
* `consecutiveTopRun_Icc`, `partBase_Icc`, `partMax_Icc`, `partSlope_Icc`: the structural
  invariants of an interval, which is the shape both pentagonal families `smkSet`/`spkSet` take
-/

@[expose] public section

open Finset

namespace PentagonalNumberTheorem.Franklin

/-- Base case: `consecutiveTopRun S 0 = 1` if `0 ∈ S`, else `0`.
@isnad1 id=eq.0h1v.s5.08280ed09b1e from=translated src=- shape=0326d7cf vocab=d8bd2917
-/
@[simp]
lemma ctr_zero (S : Finset ℕ) : consecutiveTopRun S 0 = if (0 : ℕ) ∈ S then 1 else 0 := by
  simp [consecutiveTopRun]
/-- Recurrence: `consecutiveTopRun S (m+1)` is `1 + consecutiveTopRun S m` if `m+1 ∈ S`,
else `0`.
@isnad1 id=eq.0h2v.s6.d28e2e66056f from=translated src=- shape=6abf8692 vocab=476bd15f
-/
@[simp]
lemma ctr_succ (S : Finset ℕ) (m : ℕ) :
    consecutiveTopRun S (m + 1) = if m + 1 ∈ S then 1 + consecutiveTopRun S m else 0 := by
  simp [consecutiveTopRun]
/-- If `m ∉ S` then `consecutiveTopRun S m = 0`.
@isnad1 id=eq.1h2v.s4.e337c5dfcd70 from=translated src=- shape=0ef1c6ed vocab=41d9a2a5
-/
lemma ctr_not_mem (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : consecutiveTopRun S m = 0 := by
  cases m with
  | zero => simp [h]
  | succ m => rw [ctr_succ, ite_eq_right h]
/-- If `m ∈ S` then `consecutiveTopRun S m > 0`.
@isnad1 id=lt.1h2v.s4.1773dd967f12 from=translated src=- shape=49ee4d89 vocab=1ea4077e
-/
lemma ctr_pos_of_mem (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : 0 < consecutiveTopRun S m := by
  cases m with
  | zero => simp [h]
  | succ m => rw [ctr_succ, ite_eq_left h]; omega
/-- If `0 ∉ S` then `consecutiveTopRun S m ≤ m`.
@isnad1 id=le.1h2v.s4.bf507bd33eb1 from=translated src=- shape=c93daa7a vocab=2dff1963
-/
lemma ctr_le (S : Finset ℕ) (m : ℕ) (h : (0 : ℕ) ∉ S) : consecutiveTopRun S m ≤ m := by
  induction m with
  | zero => simp [h]
  | succ m ih => rw [ctr_succ]; split_ifs <;> omega
/-- If `j < consecutiveTopRun S m` then `m - j ∈ S`.
@isnad1 id=mem.1h3v.s5.6b61cb2cf748 from=translated src=- shape=73e17434 vocab=53126fd3
-/
lemma ctr_mem_of_lt (S : Finset ℕ) (m j : ℕ) (hj : j < consecutiveTopRun S m) :
    m - j ∈ S := by
  induction m generalizing j with
  | zero =>
    rw [ctr_zero] at hj
    split_ifs at hj with h
    · obtain rfl : j = 0 := by omega
      simpa using h
    · omega
  | succ m ih =>
    rw [ctr_succ] at hj
    split_ifs at hj with h
    · cases j with
      | zero => simpa using h
      | succ j => simpa using ih j (by omega)
    · omega
/-- Lower bound for `consecutiveTopRun`: a run of length `r` below `m` forces
`r ≤ consecutiveTopRun S m`.
@isnad1 id=le.2h3v.s5.3bc01773c9a5 from=translated src=- shape=2f29a7ea vocab=acc6c0db
-/
lemma ctr_ge_of_mem (S : Finset ℕ) (m r : ℕ) (hrm : r ≤ m) (h : ∀ j < r, m - j ∈ S) :
    r ≤ consecutiveTopRun S m := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
    cases r with
    | zero => exact Nat.zero_le _
    | succ r =>
      rw [ctr_succ, ite_eq_left (by simpa using h 0 (Nat.succ_pos r))]
      have := ih r (by omega) fun j hj => by simpa using h (j + 1) (by omega)
      omega
/-- `consecutiveTopRun S m` is the unique `r ≤ m` with `m - j ∈ S` for every `j < r` and
`m - r ∉ S`.
@isnad1 id=eq.3h3v.s6.5837ce20f4bc from=translated src=- shape=d05c40a6 vocab=acc6c0db
-/
lemma ctr_eq_of (S : Finset ℕ) (m r : ℕ) (hrm : r ≤ m) (hmem : ∀ j < r, m - j ∈ S)
    (hnot : m - r ∉ S) : consecutiveTopRun S m = r :=
  le_antisymm (by by_contra hc; exact hnot (ctr_mem_of_lt S m r (by omega)))
    (ctr_ge_of_mem S m r hrm hmem)
/-- If `0 ∉ S` and `m ∈ S` then `m - consecutiveTopRun S m ∉ S`.
@isnad1 id=not.2h2v.s5.429695a4c33b from=translated src=- shape=44d1c92a vocab=340bbf4e
-/
lemma ctr_not_mem_boundary (S : Finset ℕ) (m : ℕ) (h0 : (0 : ℕ) ∉ S) (hm : m ∈ S) :
    m - consecutiveTopRun S m ∉ S := by
  induction m with
  | zero => exact absurd hm h0
  | succ m ih =>
    rw [ctr_succ, ite_eq_left hm]
    by_cases h : m ∈ S
    · rw [show m + 1 - (1 + consecutiveTopRun S m) = m - consecutiveTopRun S m by omega]
      exact ih h
    · rw [ctr_not_mem S m h]
      simpa using h
/-- `S ∈ distinctPartitions n` iff `S ⊆ Icc 1 n` and `S.sum id = n`.
@isnad1 id=iff.0h2v.s5.5df584618441 from=translated src=- shape=d4ad5ebc vocab=531ae3b3
-/
lemma mem_DP (n : ℕ) (S : Finset ℕ) :
    S ∈ distinctPartitions n ↔ S ⊆ Icc 1 n ∧ S.sum id = n := by
  simp [distinctPartitions]
/-- Every element of a distinct partition of n is positive.
@isnad1 id=le.2h3v.s5.22cbbb54cf4f from=translated src=- shape=d6686977 vocab=a9462140
-/
lemma DP_pos_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) {x : ℕ} (hx : x ∈ S) :
    1 ≤ x :=
  (mem_Icc.mp (mem_powerset.mp (mem_filter.mp hS).1 hx)).1
/-- Every element of `S ∈ distinctPartitions n` is at most n.
@isnad1 id=le.2h3v.s5.0daacd56f4bb from=translated src=- shape=e785e1f7 vocab=a9462140
-/
lemma DP_le_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) {x : ℕ} (hx : x ∈ S) :
    x ≤ n :=
  (mem_Icc.mp (mem_powerset.mp (mem_filter.mp hS).1 hx)).2
/-- `0` is not in any distinct partition.
@isnad1 id=not.1h2v.s5.dd4da02ccd7f from=translated src=- shape=060b1b69 vocab=0a7d83ca
-/
lemma DP_zero_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) : (0 : ℕ) ∉ S :=
  fun h => absurd (DP_pos_mem n S hS h) (by omega)
/-- The sum of a distinct partition of n equals n.
@isnad1 id=eq.1h2v.s5.bcd567d36b28 from=translated src=- shape=edb9ada5 vocab=b3d700ea
-/
lemma DP_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) : S.sum id = n :=
  (mem_filter.mp hS).2
/-- Every α-partition is a distinct partition.
@isnad1 id=mem.1h2v.s5.c9c3dea0418c from=translated src=- shape=55fa5289 vocab=9ddb4cb3
-/
lemma DPalpha_mem_DP (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    S ∈ distinctPartitions n :=
  (mem_filter.mp hS).1
/-- Every β-partition is a distinct partition.
@isnad1 id=mem.1h2v.s5.4ccc42de1bb9 from=translated src=- shape=55fa5289 vocab=78bb93da
-/
lemma DPbeta_mem_DP (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    S ∈ distinctPartitions n :=
  (mem_filter.mp hS).1
/-- Every α-partition is nonempty.
@isnad1 id=nonempty.1h2v.s4.ab4e0ccd4479 from=translated src=- shape=8d07ec4e vocab=674f0cf4
-/
lemma DPalpha_nonempty (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    S.Nonempty :=
  card_pos.mp (mem_filter.mp hS).2.1
/-- Every β-partition is nonempty.
@isnad1 id=nonempty.1h2v.s4.db6f13400dde from=translated src=- shape=8d07ec4e vocab=be1f0c97
-/
lemma DPbeta_nonempty (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) : S.Nonempty :=
  card_pos.mp (mem_filter.mp hS).2.1
/-- `partBase S ∈ S` for nonempty S.
@isnad1 id=mem.1h1v.s4.39798fabbff1 from=translated src=- shape=b73c1ca9 vocab=752f9115
-/
lemma partBase_mem (S : Finset ℕ) (hne : S.Nonempty) : partBase S ∈ S := by
  simp only [partBase, dite_eq_left hne]
  exact min'_mem _ hne
/-- `partMax S ∈ S` for nonempty S.
@isnad1 id=mem.1h1v.s4.8466d7b33c7d from=translated src=- shape=b73c1ca9 vocab=5c101b9d
-/
lemma partMax_mem (S : Finset ℕ) (hne : S.Nonempty) : partMax S ∈ S := by
  simp only [partMax, dite_eq_left hne]
  exact max'_mem _ hne
/-- `partBase S ≤ x` for any `x ∈ S`.
@isnad1 id=le.2h2v.s4.c82d9f16c379 from=translated src=- shape=eb5bb9dc vocab=d9f7e472
-/
lemma partBase_le (S : Finset ℕ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S) :
    partBase S ≤ x := by
  simp only [partBase, dite_eq_left hne]
  exact min'_le _ _ hx
/-- `x ≤ partMax S` for any `x ∈ S`.
@isnad1 id=le.2h2v.s4.211365ebdae5 from=translated src=- shape=bd0c1efb vocab=15d48412
-/
lemma le_partMax (S : Finset ℕ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S) :
    x ≤ partMax S := by
  simp only [partMax, dite_eq_left hne]
  exact le_max' _ _ hx
/-- `partBase S ≤ partMax S` for nonempty S.
@isnad1 id=le.1h1v.s3.e577d566da16 from=translated src=- shape=80fe97aa vocab=b1c1d37c
-/
lemma partBase_le_partMax (S : Finset ℕ) (hne : S.Nonempty) : partBase S ≤ partMax S :=
  partBase_le S hne (partMax_mem S hne)
/-- `partSlope S > 0` when `S` is nonempty.
@isnad1 id=lt.1h1v.s4.a6a7e43e0a1d from=translated src=- shape=87b1b431 vocab=1efe2672
-/
lemma partSlope_pos (S : Finset ℕ) (hne : S.Nonempty) : 0 < partSlope S :=
  ctr_pos_of_mem S _ (partMax_mem S hne)
/-- `partSlope S ≤ partMax S` when `0 ∉ S`.
@isnad1 id=le.1h1v.s4.4178e3580415 from=translated src=- shape=587b6e41 vocab=1cb3d7d8
-/
lemma partSlope_le_partMax (S : Finset ℕ) (h0 : (0 : ℕ) ∉ S) :
    partSlope S ≤ partMax S :=
  ctr_le S _ h0
/-- For S ∈ α(n), `partBase S ≤ partSlope S`.
@isnad1 id=le.1h2v.s4.51f56384f444 from=translated src=- shape=7901e57b vocab=d36c74c2
-/
lemma DPalpha_base_le_slope (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partBase S ≤ partSlope S := by
  have := (mem_filter.mp hS).2.2
  omega
/-- For S ∈ β(n), `partSlope S < partBase S`.
@isnad1 id=lt.1h2v.s4.6a8dcbb0c67b from=translated src=- shape=7901e57b vocab=962a24b5
-/
lemma DPbeta_slope_lt_base (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partSlope S < partBase S := by
  have := (mem_filter.mp hS).2.2
  omega
/-- The bottom of the top run, `partMax S - partSlope S + 1`, is an element of `S`, hence is
at least `partBase S`. This is the common core of `DPalpha_max_ge_2base` and
`DPbeta_max_ge_2slope_add_1`. -/
private lemma base_le_max_sub_slope_add_one (S : Finset ℕ) (hne : S.Nonempty)
    (h0 : (0 : ℕ) ∉ S) : partBase S ≤ partMax S - partSlope S + 1 := by
  have hs := partSlope_pos S hne
  have hsm := partSlope_le_partMax S h0
  have := partBase_le S hne
    (ctr_mem_of_lt S (partMax S) (partSlope S - 1) (by change partSlope S - 1 < partSlope S; omega))
  omega
/-- For S ∈ α(n), `partMax S ≥ 2 * partBase S`.
@isnad1 id=le.1h2v.s5.f34df61bc33c from=translated src=- shape=5f141e51 vocab=2ec7e6dc
-/
lemma DPalpha_max_ge_2base (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    2 * partBase S ≤ partMax S := by
  have hne := DPalpha_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPalpha_mem_DP n S hS)
  have := base_le_max_sub_slope_add_one S hne h0
  have := partSlope_pos S hne
  have := partSlope_le_partMax S h0
  have := (mem_filter.mp hS).2.2
  omega
/-- For S ∈ β(n), `partMax S ≥ 2 * partSlope S + 1`.
@isnad1 id=le.1h2v.s5.72f8efeba779 from=translated src=- shape=c5e4c25c vocab=233eda16
-/
lemma DPbeta_max_ge_2slope_add_1 (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    2 * partSlope S + 1 ≤ partMax S := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have := base_le_max_sub_slope_add_one S hne h0
  have := partSlope_pos S hne
  have := partSlope_le_partMax S h0
  have := (mem_filter.mp hS).2.2
  omega

/-! ### Intervals

Both pentagonal families are intervals — `smkSet k = Icc k (2 * k - 1)` and
`spkSet k = Icc (k + 1) (2 * k)` — and a *special* partition is an interval too
(`DPspecial_*` in `Lemmas.lean`). The lemmas below compute the sum and the three structural
invariants of an arbitrary `Finset.Icc a b` once and for all. -/

/-- Gauss' summation formula over `Finset.Icc` in `ℕ`, in `* 2` form: no division and no
truncated subtraction on the left. Unconditional — both sides are `0` when `b < a`.
@isnad1 id=eq.0h2v.s6.f889e03427a0 from=translated src=- shape=de5a7920 vocab=d35a80a1
-/
theorem sum_Icc_id_mul_two (a b : ℕ) : (∑ i ∈ Icc a b, i) * 2 = (b + 1 - a) * (a + b) := by
  rcases le_or_gt a b with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    have hc : a + n + 1 - a = n + 1 := by omega
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, hc, sum_add_distrib, sum_const,
      card_range, smul_eq_mul, add_mul, sum_range_id_mul_two, Nat.add_sub_cancel]
    ring
  · rw [Icc_eq_empty (by omega), sum_empty, Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul,
      Nat.zero_mul]

/-- Gauss' summation formula over `Finset.Icc` in `ℕ`.
@isnad1 id=eq.0h2v.s6.2ca5bcfcc0d1 from=translated src=- shape=f166f3f2 vocab=3d9c17c5
-/
theorem sum_Icc_id (a b : ℕ) : ∑ i ∈ Icc a b, i = (b + 1 - a) * (a + b) / 2 := by
  rw [← sum_Icc_id_mul_two, Nat.mul_div_cancel _ Nat.zero_lt_two]

/-- `sum_Icc_id_mul_two` in `Finset.sum _ id` phrasing, which is what `distinctPartitions` uses.
`rw` cannot see through `id`, so this restatement is what call sites need.
@isnad1 id=eq.0h2v.s6.21441eff70bb from=translated src=- shape=e19d01c4 vocab=bbe2bdb8
-/
theorem Icc_sum_id_mul_two (a b : ℕ) : (Icc a b).sum id * 2 = (b + 1 - a) * (a + b) :=
  sum_Icc_id_mul_two a b

/-- `sum_Icc_id` in `Finset.sum _ id` phrasing.
@isnad1 id=eq.0h2v.s6.c21de064f784 from=translated src=- shape=f8fa4734 vocab=f9ba71df
-/
theorem Icc_sum_id (a b : ℕ) : (Icc a b).sum id = (b + 1 - a) * (a + b) / 2 :=
  sum_Icc_id a b

/-- The consecutive-run function on an interval: every element of `Icc a b` continues the run
back down to `a`, and everything outside has run length `0`.
@isnad1 id=eq.0h3v.s6.8b2f4b7bf774 from=translated src=- shape=662d43a1 vocab=8c3e7697
-/
theorem consecutiveTopRun_Icc (a b m : ℕ) :
    consecutiveTopRun (Icc a b) m = if a ≤ m ∧ m ≤ b then m - a + 1 else 0 := by
  induction m with
  | zero => simp only [ctr_zero, mem_Icc]; split_ifs <;> omega
  | succ m ih => rw [ctr_succ, ih]; simp only [mem_Icc]; split_ifs <;> omega

/-- The base of a nonempty interval is its left endpoint.
@isnad1 id=eq.1h2v.s4.d29c41240fc6 from=translated src=- shape=3894de3f vocab=12d9069e
-/
theorem partBase_Icc {a b : ℕ} (hab : a ≤ b) : partBase (Icc a b) = a := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  simp only [partBase, dite_eq_left hne]
  exact le_antisymm (min'_le _ _ (mem_Icc.mpr ⟨le_rfl, hab⟩))
    (le_min' _ _ _ fun x hx => (mem_Icc.mp hx).1)

/-- The max of a nonempty interval is its right endpoint.
@isnad1 id=eq.1h2v.s4.eeacf320864c from=translated src=- shape=6e3b468d vocab=b166caaa
-/
theorem partMax_Icc {a b : ℕ} (hab : a ≤ b) : partMax (Icc a b) = b := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  simp only [partMax, dite_eq_left hne]
  exact le_antisymm (max'_le _ _ _ fun x hx => (mem_Icc.mp hx).2)
    (le_max' _ _ (mem_Icc.mpr ⟨hab, le_rfl⟩))

/-- A nonempty interval is one single run, so its slope is its whole length.
@isnad1 id=eq.1h2v.s5.506e7de0de7f from=translated src=- shape=cae5bb58 vocab=f6ce6069
-/
theorem partSlope_Icc {a b : ℕ} (hab : a ≤ b) : partSlope (Icc a b) = b - a + 1 := by
  rw [partSlope, partMax_Icc hab, consecutiveTopRun_Icc, ite_eq_left ⟨hab, le_rfl⟩]

/-- For S ∈ α(n), `partMax S - partBase S + 1 ∈ S`.
@isnad1 id=mem.1h2v.s5.516b4646bb54 from=translated src=- shape=fd229d46 vocab=a832769a
-/
lemma DPalpha_m_sub_b_add_1_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partMax S - partBase S + 1 ∈ S := by
  have hne := DPalpha_nonempty n S hS
  have hb1 : 1 ≤ partBase S := DP_pos_mem n S (DPalpha_mem_DP n S hS) (partBase_mem S hne)
  have hbm := partBase_le_partMax S hne
  have hbs := DPalpha_base_le_slope n S hS
  have h := ctr_mem_of_lt S (partMax S) (partBase S - 1)
    (by change partBase S - 1 < partSlope S; omega)
  rwa [show partMax S - (partBase S - 1) = partMax S - partBase S + 1 by omega] at h
/-- For S ∈ α(n), `partBase S ≠ partMax S - partBase S + 1`.
@isnad1 id=ne.1h2v.s5.8ecd54e0f280 from=translated src=- shape=aa13d2a5 vocab=a832769a
-/
lemma DPalpha_base_ne_m_sub_b_add_1 (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partBase S ≠ partMax S - partBase S + 1 := by
  have := DPalpha_max_ge_2base n S hS
  omega
/-- `partMax S + 1 ∉ S` for nonempty S.
@isnad1 id=not.1h1v.s5.210b80b59423 from=translated src=- shape=6e039b1f vocab=ea238b02
-/
lemma partMax_succ_not_mem (S : Finset ℕ) (hne : S.Nonempty) :
    partMax S + 1 ∉ S :=
  fun h => absurd (le_partMax S hne h) (by omega)
/-- Membership in `αOp S`, with the two `let`s of the definition unfolded.
@isnad1 id=iff.0h2v.s6.9504e8d2f37c from=translated src=- shape=a47a2f8d vocab=0a5a4708
-/
lemma mem_alphaOp {S : Finset ℕ} {x : ℕ} :
    x ∈ alphaOp S ↔
      x = partMax S + 1 ∨ (x ≠ partMax S - partBase S + 1 ∧ x ≠ partBase S ∧ x ∈ S) := by
  simp only [alphaOp, mem_insert, mem_erase]
/-- The α-operation preserves the sum of parts.
@isnad1 id=eq.1h2v.s5.f4acd6ef36c2 from=translated src=- shape=f33884c5 vocab=5ce343a0
-/
lemma alphaOp_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    (alphaOp S).sum id = S.sum id := by
  have hne := DPalpha_nonempty n S hS
  have hbm := partBase_le_partMax S hne
  have hb : partBase S ∈ S := partBase_mem S hne
  have hm1 : partMax S - partBase S + 1 ∈ S.erase (partBase S) :=
    mem_erase.mpr ⟨(DPalpha_base_ne_m_sub_b_add_1 n S hS).symm, DPalpha_m_sub_b_add_1_mem n S hS⟩
  have hins : partMax S + 1 ∉ (S.erase (partBase S)).erase (partMax S - partBase S + 1) :=
    fun h => partMax_succ_not_mem S hne (mem_of_mem_erase (mem_of_mem_erase h))
  have key : S.sum id
      = ((S.erase (partBase S)).erase (partMax S - partBase S + 1)).sum id
        + (partMax S - partBase S + 1) + partBase S := by
    rw [← sum_erase_add S id hb, ← sum_erase_add _ id hm1]
    rfl
  rw [show alphaOp S = insert (partMax S + 1)
        ((S.erase (partBase S)).erase (partMax S - partBase S + 1)) from rfl,
    sum_insert hins, key]
  simp only [id_eq]
  omega
/-- For S ∈ α(n), `partMax (αOp S) = partMax S + 1`.
@isnad1 id=eq.1h2v.s5.844dba85e5f5 from=translated src=- shape=95c294a2 vocab=19ffe85e
-/
lemma alphaOp_partMax (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partMax (alphaOp S) = partMax S + 1 := by
  have hne := DPalpha_nonempty n S hS
  have hmem : partMax S + 1 ∈ alphaOp S := mem_alphaOp.mpr (Or.inl rfl)
  have hneA : (alphaOp S).Nonempty := ⟨_, hmem⟩
  have hub : ∀ x ∈ alphaOp S, x ≤ partMax S + 1 := by
    intro x hx
    rcases mem_alphaOp.mp hx with rfl | ⟨-, -, hxS⟩
    · exact le_rfl
    · exact Nat.le_succ_of_le (le_partMax S hne hxS)
  simp only [partMax, dite_eq_left hneA]
  exact le_antisymm (max'_le _ _ _ hub) (le_max' _ _ hmem)
/-- For S ∈ α(n), `partSlope (αOp S) = partBase S`.
@isnad1 id=eq.1h2v.s4.ca6d3bf10c69 from=translated src=- shape=9e4b4098 vocab=8b83ef88
-/
lemma alphaOp_partSlope (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partSlope (alphaOp S) = partBase S := by
  have hne := DPalpha_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPalpha_mem_DP n S hS)
  have hb1 : 1 ≤ partBase S := DP_pos_mem n S (DPalpha_mem_DP n S hS) (partBase_mem S hne)
  have hbm := partBase_le_partMax S hne
  have h2b := DPalpha_max_ge_2base n S hS
  have hbs := DPalpha_base_le_slope n S hS
  have hsm := partSlope_le_partMax S h0
  rw [partSlope, alphaOp_partMax n S hS]
  refine ctr_eq_of _ _ _ (by omega) (fun j hj => ?_) ?_
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact mem_alphaOp.mpr (Or.inl (by omega))
    · have h := ctr_mem_of_lt S (partMax S) (j - 1) (by change j - 1 < partSlope S; omega)
      rw [show partMax S - (j - 1) = partMax S + 1 - j by omega] at h
      exact mem_alphaOp.mpr (Or.inr ⟨by omega, by omega, h⟩)
  · rw [show partMax S + 1 - partBase S = partMax S - partBase S + 1 by omega]
    intro hmem
    rcases mem_alphaOp.mp hmem with h | ⟨h, -, -⟩
    · omega
    · exact h rfl
/-- For S ∈ β(n), `partSlope S ∉ S`.
@isnad1 id=not.1h2v.s5.8bc6a820ada3 from=translated src=- shape=e934b4b6 vocab=5f02b1da
-/
lemma DPbeta_slope_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partSlope S ∉ S := fun h =>
  absurd (partBase_le S (DPbeta_nonempty n S hS) h)
    (by have := DPbeta_slope_lt_base n S hS; omega)
/-- For S ∈ β(n), `partMax S - partSlope S ∉ S`.
@isnad1 id=not.1h2v.s5.d90e4567018f from=translated src=- shape=faffdf97 vocab=371ff000
-/
lemma DPbeta_m_sub_s_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partMax S - partSlope S ∉ S :=
  ctr_not_mem_boundary S (partMax S) (DP_zero_not_mem n S (DPbeta_mem_DP n S hS))
    (partMax_mem S (DPbeta_nonempty n S hS))
/-- For S ∈ β(n), `partSlope S ≠ partMax S - partSlope S`.
@isnad1 id=ne.1h2v.s5.b93115c86ee1 from=translated src=- shape=2a180b9a vocab=371ff000
-/
lemma DPbeta_slope_ne_m_sub_slope (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partSlope S ≠ partMax S - partSlope S := by
  have := DPbeta_max_ge_2slope_add_1 n S hS
  omega
/-- For S ∈ β(n), `βOp S` inserts the slope and `partMax S - partSlope S` into `S`, after
deleting the maximum.
@isnad1 id=eq.1h2v.s5.a3f8b3564754 from=translated src=- shape=99dcccad vocab=46954f43
-/
lemma betaOp_eq (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    betaOp S
      = insert (partSlope S) (insert (partMax S - partSlope S) (S.erase (partMax S))) := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have := partSlope_pos S hne
  have := DPbeta_max_ge_2slope_add_1 n S hS
  simp only [betaOp, erase_insert_of_ne (by omega : partSlope S ≠ partMax S),
    erase_insert_of_ne (by omega : partMax S - partSlope S ≠ partMax S)]
/-- The β-operation preserves the sum of parts.
@isnad1 id=eq.1h2v.s5.1a26e2b3c44a from=translated src=- shape=f33884c5 vocab=c0416e38
-/
lemma betaOp_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    (betaOp S).sum id = S.sum id := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have hsm := partSlope_le_partMax S h0
  have hmS : partMax S ∈ S := partMax_mem S hne
  have hsS := DPbeta_slope_not_mem n S hS
  have hmsS := DPbeta_m_sub_s_not_mem n S hS
  have hs_ne := DPbeta_slope_ne_m_sub_slope n S hS
  rw [betaOp_eq n S hS, sum_insert (by simp [hs_ne, hsS]),
    sum_insert (fun h => hmsS (mem_of_mem_erase h)), ← sum_erase_add S id hmS]
  simp only [id_eq]
  omega
/-- For S ∈ β(n), `partMax (βOp S) = partMax S - 1`.
@isnad1 id=eq.1h2v.s5.2129da23d222 from=translated src=- shape=95c294a2 vocab=3772b724
-/
lemma betaOp_partMax (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partMax (betaOp S) = partMax S - 1 := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have hs0 := partSlope_pos S hne
  have h2s := DPbeta_max_ge_2slope_add_1 n S hS
  have hmem : partMax S - 1 ∈ betaOp S := by
    rw [betaOp_eq n S hS]
    by_cases h : partSlope S = 1
    · exact mem_insert_of_mem (by rw [h]; exact mem_insert_self _ _)
    · refine mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨by omega, ?_⟩))
      exact ctr_mem_of_lt S (partMax S) 1 (by change (1 : ℕ) < partSlope S; omega)
  have hneB : (betaOp S).Nonempty := ⟨_, hmem⟩
  have hub : ∀ x ∈ betaOp S, x ≤ partMax S - 1 := by
    intro x hx
    rw [betaOp_eq n S hS] at hx
    simp only [mem_insert, mem_erase] at hx
    rcases hx with rfl | rfl | ⟨hxm, hxS⟩
    · omega
    · omega
    · have := le_partMax S hne hxS; omega
  simp only [partMax, dite_eq_left hneB]
  exact le_antisymm (max'_le _ _ _ hub) (le_max' _ _ hmem)
/-- For S ∈ β(n), `partBase (βOp S) = partSlope S`.
@isnad1 id=eq.1h2v.s4.4457d2da6a7b from=translated src=- shape=9e4b4098 vocab=05c99f70
-/
lemma betaOp_partBase (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partBase (betaOp S) = partSlope S := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have h2s := DPbeta_max_ge_2slope_add_1 n S hS
  have hsb := DPbeta_slope_lt_base n S hS
  have hmem : partSlope S ∈ betaOp S := by
    rw [betaOp_eq n S hS]; exact mem_insert_self _ _
  have hneB : (betaOp S).Nonempty := ⟨_, hmem⟩
  have hlb : ∀ x ∈ betaOp S, partSlope S ≤ x := by
    intro x hx
    rw [betaOp_eq n S hS] at hx
    simp only [mem_insert, mem_erase] at hx
    rcases hx with rfl | rfl | ⟨-, hxS⟩
    · exact le_rfl
    · omega
    · have := partBase_le S hne hxS; omega
  simp only [partBase, dite_eq_left hneB]
  exact le_antisymm (min'_le _ _ hmem) (le_min' _ _ _ hlb)

end PentagonalNumberTheorem.Franklin
