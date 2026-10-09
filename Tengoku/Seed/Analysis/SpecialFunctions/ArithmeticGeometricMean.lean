/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecificLimits.Basic
public import Tengoku.Seed.Analysis.Real.Sqrt

/-!
# The arithmetic-geometric mean

Starting with two nonnegative real numbers, repeatedly replace them with their arithmetic and
geometric means. By the AM-GM inequality, the smaller number (geometric mean) will monotonically
increase and the larger number (arithmetic mean) will monotonically decrease.

The two monotone sequences converge to the same limit – the arithmetic-geometric mean (AGM).
This file defines the AGM in the `NNReal` namespace and proves some of its basic properties.

## References

* https://en.wikipedia.org/wiki/Arithmetic–geometric_mean
-/

@[expose] public section

namespace NNReal

/-- The AM–GM inequality for two `NNReal`s, with means in canonical form.
@isnad1 id=le.0h2v.s6.2768254fd352 from=seed src=0 shape=1931ac9e vocab=01473e56
-/
lemma sqrt_mul_le_half_add (x y : ℝ≥0) : sqrt (x * y) ≤ (x + y) / 2 := by
  rw [sqrt_le_iff_le_sq, div_pow, le_div_iff₀' (by positivity), ← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

/-- The strict AM–GM inequality for two `NNReal`s, with means in canonical form.
@isnad1 id=lt.1h2v.s6.4a0ccddbee4e from=seed src=0 shape=f18db9d4 vocab=0c2d6735
-/
lemma sqrt_mul_lt_half_add_of_ne {x y : ℝ≥0} (h : x ≠ y) : sqrt (x * y) < (x + y) / 2 := by
  wlog hl : y < x generalizing x y
  · specialize this h.symm (h.gt_or_lt.resolve_left hl)
    rwa [mul_comm, add_comm]
  have key : 0 < (x - y) ^ 2 := sq_pos_iff.mpr (by rwa [← zero_lt_iff, tsub_pos_iff_lt])
  rw [sq, tsub_mul, mul_tsub, mul_tsub, tsub_tsub_eq_add_tsub_of_le (by gcongr),
    tsub_add_eq_add_tsub (by gcongr), tsub_tsub, show x * y + y * x = 2 * x * y by ring,
    tsub_pos_iff_lt, ← sq, ← sq] at key
  rw [← sqrt_sq (_ / 2), sqrt_lt_sqrt, div_pow, lt_div_iff₀' (by positivity),
    show (2 : ℝ≥0) ^ 2 * (x * y) = 2 * x * y + 2 * x * y by ring, add_sq, add_right_comm]
  gcongr

open Function Filter Topology

/-- `agmSequences x y` is the sequence of (geometric, arithmetic) means
converging to the arithmetic-geometric mean starting from `x` and `y`. -/
noncomputable def agmSequences (x y : ℝ≥0) : ℕ → ℝ≥0 × ℝ≥0 :=
  fun n ↦ (fun p ↦ (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)

variable {x y : ℝ≥0} {n : ℕ}

/--
@isnad1 id=eq.0h2v.s6.9e74bee91f91 from=seed src=0 shape=09449a64 vocab=aee593ad
-/
@[simp]
lemma agmSequences_zero : agmSequences x y 0 = (sqrt (x * y), (x + y) / 2) := rfl

/--
@isnad1 id=eq.0h3v.s6.c0c3cef4f647 from=seed src=0 shape=efd7e264 vocab=7a839a1e
-/
lemma agmSequences_succ : agmSequences x y (n + 1) = agmSequences (sqrt (x * y)) ((x + y) / 2) n :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.eeaec1dbcc54 from=seed src=0 shape=d96500f4 vocab=373aab2e
-/
lemma agmSequences_succ' :
    agmSequences x y (n + 1) =
    (sqrt ((agmSequences x y n).1 * (agmSequences x y n).2),
      ((agmSequences x y n).1 + (agmSequences x y n).2) / 2) := by
  rw [agmSequences, agmSequences, iterate_succ', comp_apply]

/--
@isnad1 id=eq.0h2v.s4.0724cb8c49e9 from=seed src=0 shape=94996a75 vocab=4711d27c
-/
lemma agmSequences_comm : agmSequences x y = agmSequences y x := by
  funext n
  cases n with
  | zero => simp [mul_comm, add_comm]
  | succ n => simp [agmSequences_succ, mul_comm, add_comm]

/--
@isnad1 id=and.1h2v.s6.da2ffafbb05c from=seed src=0 shape=5d924c67 vocab=01473e56
-/
lemma le_gm_and_am_le (h : x ≤ y) : x ≤ sqrt (x * y) ∧ (x + y) / 2 ≤ y := by
  constructor
  · rw [le_sqrt_iff_sq_le, sq]
    gcongr
  · apply div_le_of_le_mul'
    rw [two_mul]
    gcongr

/--
@isnad1 id=le.0h2v.s6.495a1f4d61fc from=seed src=0 shape=7759e8a8 vocab=31862b59
-/
lemma dist_gm_am_le : dist (sqrt (x * y)) ((x + y) / 2) ≤ dist x y / 2 := by
  wlog h : x ≤ y generalizing x y
  · simpa [add_comm, mul_comm, dist_comm] using this (not_le.mp h).le
  rw [dist_comm, dist_eq, ← NNReal.coe_sub (sqrt_mul_le_half_add ..), abs_eq]
  calc
    _ ≤ ((x + y) / 2 - x).toReal := by
      gcongr
      rw [le_sqrt_iff_sq_le, sq]
      gcongr
    _ = _ := by
      nth_rw 2 [← add_halves x]
      rw [add_div, add_tsub_add_eq_tsub_left, ← tsub_div, NNReal.coe_div, NNReal.coe_two, dist_comm,
        dist_eq, ← NNReal.coe_sub h, abs_eq]

/--
@isnad1 id=and.0h2v.s5.56064ba9b9d0 from=seed src=0 shape=7bd7718d vocab=436948e1
-/
lemma agmSequences_monotone_and_antitone :
    (Monotone fun n ↦ (agmSequences x y n).1) ∧ Antitone fun n ↦ (agmSequences x y n).2 := by
  suffices ∀ n, (agmSequences x y n).1 ≤ (agmSequences x y (n + 1)).1 ∧
      (agmSequences x y (n + 1)).2 ≤ (agmSequences x y n).2 from
    ⟨monotone_nat_of_le_succ (this · |>.1), antitone_nat_of_succ_le (this · |>.2)⟩
  intro n
  induction n generalizing x y with
  | zero => exact le_gm_and_am_le (sqrt_mul_le_half_add ..)
  | succ n ih => exact Prod.mk_le_mk.mp ih

/--
@isnad1 id=monotone.0h2v.s4.aa14e104b9a4 from=seed src=0 shape=d5bed07b vocab=0aab0d71
-/
lemma agmSequences_fst_monotone : Monotone fun n ↦ (agmSequences x y n).1 :=
  agmSequences_monotone_and_antitone.1

/--
@isnad1 id=antitone.0h2v.s4.de13a43d686e from=seed src=0 shape=d5bed07b vocab=2e543523
-/
lemma agmSequences_snd_antitone : Antitone fun n ↦ (agmSequences x y n).2 :=
  agmSequences_monotone_and_antitone.2

/--
@isnad1 id=le.0h4v.s4.aa0cbc99bc83 from=seed src=0 shape=f7c81ebd vocab=c60b6484
-/
lemma agmSequences_fst_le_snd (n m : ℕ) : (agmSequences x y n).1 ≤ (agmSequences x y m).2 := by
  suffices ∀ {k}, (agmSequences x y k).1 ≤ (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans this
    · exact this.trans (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_le_half_add ..
  | succ n ih => exact ih

/--
@isnad1 id=lt.1h4v.s5.dd618f878af5 from=seed src=0 shape=c6d09b5e vocab=3c11c08a
-/
lemma agmSequences_fst_lt_snd_of_ne (h : x ≠ y) (n m : ℕ) :
    (agmSequences x y n).1 < (agmSequences x y m).2 := by
  suffices ∀ {k}, (agmSequences x y k).1 < (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans_lt this
    · exact this.trans_le (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_lt_half_add_of_ne h
  | succ n ih =>
    rw [agmSequences_succ']
    exact sqrt_mul_lt_half_add_of_ne (ih h).ne

/--
@isnad1 id=eq.0h2v.s4.6f2733053621 from=seed src=0 shape=2a37159b vocab=5628925b
-/
lemma agmSequences_min_max : agmSequences (min x y) (max x y) = agmSequences x y := by
  obtain h | h := le_total x y
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, agmSequences_comm]

/--
@isnad1 id=le.0h3v.s6.c2f15a87ea7d from=seed src=0 shape=4f29db16 vocab=145e0d94
-/
lemma dist_agmSequences_fst_snd (n : ℕ) :
    dist (agmSequences x y n).1 (agmSequences x y n).2 ≤ dist x y / 2 ^ (n + 1) := by
  induction n with
  | zero => simp [dist_gm_am_le]
  | succ n ih =>
    rw [agmSequences_succ']
    apply dist_gm_am_le.trans
    rw [pow_succ, ← div_div]
    gcongr

/--
@isnad1 id=tendsto.0h2v.s5.df208feed75c from=seed src=0 shape=44d95fbd vocab=3f971da6
-/
lemma tendsto_dist_agmSequences_atTop_zero :
    Tendsto (fun n ↦ dist (agmSequences x y n).1 (agmSequences x y n).2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ dist_nonneg) dist_agmSequences_fst_snd
  conv =>
    rw [← zero_mul (dist x y / 2)]
    enter [1, n]
    rw [pow_succ', ← div_div, div_eq_inv_mul, ← inv_pow]
  exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _

/-- The arithmetic-geometric mean of two `NNReal`s, defined as the infimum of arithmetic means. -/
noncomputable def agm (x y : ℝ≥0) : ℝ≥0 :=
  ⨅ n, (agmSequences x y n).2

/--
@isnad1 id=eq.0h2v.s3.060a139a7651 from=seed src=0 shape=1013c0ce vocab=4a76afd0
-/
lemma agm_comm : agm x y = agm y x := by
  unfold agm
  conv_rhs =>
    enter [1, n]
    rw [agmSequences_comm]

/--
@isnad1 id=eq.0h2v.s5.75d260e2bf13 from=seed src=0 shape=9c7b9888 vocab=6a306340
-/
lemma agm_eq_ciInf : agm x y = ⨅ n, (agmSequences x y n).2 := rfl

/--
@isnad1 id=tendsto.0h2v.s4.1053e1489ca0 from=seed src=0 shape=57e3824b vocab=7bca2d68
-/
lemma tendsto_agmSequences_snd_agm : Tendsto (fun n ↦ (agmSequences x y n).2) atTop (𝓝 (agm x y)) :=
  tendsto_atTop_ciInf agmSequences_snd_antitone (OrderBot.bddBelow _)

/--
@isnad1 id=le.0h3v.s4.1a03451d801b from=seed src=0 shape=9ff17d44 vocab=c0d90a4f
-/
lemma agm_le_agmSequences_snd (n : ℕ) : agm x y ≤ (agmSequences x y n).2 := ciInf_le' _ n

/--
@isnad1 id=le.0h2v.s4.5820d5680cc9 from=seed src=0 shape=42e73927 vocab=cdce594a
-/
lemma agm_le_max : agm x y ≤ max x y := by
  wlog h : x ≤ y generalizing x y
  · simpa [agm_comm, max_comm] using this (not_le.mp h).le
  rw [max_eq_right h]
  apply (agm_le_agmSequences_snd 0).trans
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).2

/--
@isnad1 id=bddabove.0h2v.s4.f39b12498359 from=seed src=0 shape=a02483bd vocab=d5981d15
-/
lemma bddAbove_range_agmSequences_fst : BddAbove (Set.range fun n ↦ (agmSequences x y n).1) := by
  rw [bddAbove_def]
  use (agmSequences x y 0).2
  simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ ↦ agmSequences_fst_le_snd ..

/-- The AGM is also the supremum of the geometric means.
@isnad1 id=eq.0h2v.s5.bf17e794fe35 from=seed src=0 shape=9c7b9888 vocab=b13d3e29
-/
lemma agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).1 := by
  refine tendsto_nhds_unique (tendsto_agmSequences_snd_agm.congr_dist ?_)
    (tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst)
  conv =>
    enter [1, n]
    rw [dist_comm]
  exact tendsto_dist_agmSequences_atTop_zero

/--
@isnad1 id=tendsto.0h2v.s4.665c8c8e50ee from=seed src=0 shape=57e3824b vocab=0b0b9780
-/
lemma tendsto_agmSequences_fst_agm :
    Tendsto (fun n ↦ (agmSequences x y n).1) atTop (𝓝 (agm x y)) := by
  rw [agm_eq_ciSup]
  exact tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst

/--
@isnad1 id=le.0h3v.s4.1dbdee223369 from=seed src=0 shape=d9c7a85c vocab=97147cb6
-/
lemma agmSequences_fst_le_agm (n : ℕ) : (agmSequences x y n).1 ≤ agm x y := by
  rw [agm_eq_ciSup]
  exact le_ciSup bddAbove_range_agmSequences_fst _

/--
@isnad1 id=le.0h2v.s4.d88f97bb6428 from=seed src=0 shape=fd88313c vocab=3aac4281
-/
lemma min_le_agm : min x y ≤ agm x y := by
  wlog h : x ≤ y generalizing x y
  · simpa [agm_comm, min_comm] using this (not_le.mp h).le
  rw [min_eq_left h]
  refine le_trans ?_ (agmSequences_fst_le_agm 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).1

/--
@isnad1 id=eq.0h1v.s3.df4d08f50584 from=seed src=0 shape=ca6c1f5d vocab=4a76afd0
-/
@[simp]
lemma agm_self : agm x x = x := by
  apply le_antisymm
  · nth_rw 3 [← max_self x]
    exact agm_le_max
  · nth_rw 1 [← min_self x]
    exact min_le_agm

/--
@isnad1 id=eq.0h1v.s4.b7debafed294 from=seed src=0 shape=fe2c2146 vocab=4a76afd0
-/
@[simp]
lemma agm_zero_left : agm 0 y = 0 := by
  suffices ∀ n, (agmSequences 0 y n).1 = 0 by simp [agm_eq_ciSup, this]
  intro n
  induction n with
  | zero => simp [agmSequences]
  | succ n ih =>
    rw [agmSequences_succ', ih, zero_mul, sqrt_zero]

/--
@isnad1 id=eq.0h1v.s4.22c39b675041 from=seed src=0 shape=1d838610 vocab=4a76afd0
-/
@[simp]
lemma agm_zero_right : agm x 0 = 0 := by
  rw [agm_comm, agm_zero_left]

/--
@isnad1 id=lt.2h2v.s5.37a90e0288f2 from=seed src=0 shape=6c67d60b vocab=cbff4915
-/
lemma agm_pos (hx : 0 < x) (hy : 0 < y) : 0 < agm x y := (lt_min hx hy).trans_le min_le_agm

/--
@isnad1 id=eq.0h3v.s4.3329c3681c9e from=seed src=0 shape=2972ee00 vocab=fd8e05c2
-/
lemma agm_eq_agm_agmSequences_fst_agmSequences_snd (n : ℕ) :
    agm x y = agm (agmSequences x y n).1 (agmSequences x y n).2 := by
  refine tendsto_nhds_unique ?_ tendsto_agmSequences_snd_agm
  have key := @tendsto_agmSequences_snd_agm x y
  rw [← tendsto_add_atTop_iff_nat (n + 1)] at key
  convert! key using 2 with m
  simp_rw [agmSequences, Prod.mk.eta, ← iterate_add_apply, add_right_comm]

/--
@isnad1 id=eq.0h2v.s6.23deaabde459 from=seed src=0 shape=62a01f02 vocab=fdc589a9
-/
lemma agm_eq_agm_gm_am : agm x y = agm (sqrt (x * y)) ((x + y) / 2) := by
  simpa using agm_eq_agm_agmSequences_fst_agmSequences_snd 0

/--
@isnad1 id=lt.3h3v.s5.27ebda9f7602 from=seed src=0 shape=33b6f4e6 vocab=65b93d61
-/
lemma agmSequences_fst_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x ≠ y) (n : ℕ) :
    (agmSequences x y n).1 < agm x y := by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (?_ : p < sqrt (p * q)).trans_le (agmSequences_fst_le_agm 0)
  have ppos : 0 < p :=
    (show 0 < sqrt (x * y) by positivity).trans_le (agmSequences_fst_monotone zero_le)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 1 [← mul_self_sqrt p, sqrt_mul]
  gcongr

/--
@isnad1 id=lt.1h3v.s4.9797b0878365 from=seed src=0 shape=0c4b489e vocab=60e1ce94
-/
lemma agm_lt_agmSequences_snd_of_ne (hn : x ≠ y) (n : ℕ) : agm x y < (agmSequences x y n).2 := by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (agm_le_agmSequences_snd 0).trans_lt (?_ : (p + q) / 2 < q)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 2 [← add_halves q]
  rw [add_div]
  gcongr

/--
@isnad1 id=lt.3h2v.s5.123430c03193 from=seed src=0 shape=10d03c83 vocab=80405f48
-/
lemma min_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x ≠ y) : min x y < agm x y := by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, min_comm] using this hy hx hn.symm (hn.gt_or_lt.resolve_right h)
  rw [min_eq_left h.le]
  refine lt_of_le_of_lt ?_ (agmSequences_fst_lt_agm_of_pos_of_ne hx hy hn 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).1

/--
@isnad1 id=lt.1h2v.s4.e8ee55a35ef7 from=seed src=0 shape=00d77149 vocab=8354a9b5
-/
lemma agm_lt_max_of_ne (hn : x ≠ y) : agm x y < max x y := by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, max_comm] using this hn.symm (hn.gt_or_lt.resolve_right h)
  rw [max_eq_right h.le]
  apply (agm_lt_agmSequences_snd_of_ne hn 0).trans_le
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).2

/-- The AGM distributes over multiplication.
@isnad1 id=eq.0h3v.s5.3ff52c7499dc from=seed src=0 shape=eeef3b55 vocab=4aac3fb2
-/
lemma agm_mul_distrib {k : ℝ≥0} : agm (k * x) (k * y) = k * agm x y := by
  simp_rw [agm, mul_iInf]
  congr! with n
  induction n generalizing x y with
  | zero => simp [← mul_div_assoc, mul_add]
  | succ n ih =>
    rw [agmSequences_succ, ← mul_add, mul_div_assoc, mul_mul_mul_comm,
      ← sq, sqrt_mul, sqrt_sq, ih, agmSequences_succ]

end NNReal
