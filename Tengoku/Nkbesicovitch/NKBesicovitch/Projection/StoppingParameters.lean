/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
public import Tengoku.Seed.Tactic.FieldSimp
public import Tengoku.Seed.Tactic.Linarith
public import Tengoku.Seed.Tactic.NormNum
public import Tengoku.Seed.Tactic.Positivity
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parameters for finite-depth corner stopping

The density exponent decreases from `100` to `0`; the loss exponent
increases by `1 / J²` at each level. This gap lets the total child deletion
fit inside half the mass promised by the selected parent.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- Exponent controlling the density threshold at level `i` of a depth-`J` tree.-/
noncomputable def stoppingRho (J i : ℕ) : ℝ := 100 * (1 - (i : ℝ) / J)

/-- Exponent controlling the allowed deletion at level `i` of a depth-`J` tree.-/
noncomputable def stoppingAlpha (J i : ℕ) : ℝ := 1 / J + (i : ℝ) / (J : ℝ) ^ 2

/--
@isnad1 id=eq.0h1v.s4.4d7ef40c243a from=translated src=- shape=8fc7241c vocab=11720168
-/
theorem stoppingRho_zero (J : ℕ) : stoppingRho J 0 = 100 := by simp [stoppingRho]

/--
@isnad1 id=eq.1h1v.s4.5ace912a4735 from=translated src=- shape=9d19c5de vocab=aa202fc8
-/
theorem stoppingRho_self {J : ℕ} (hJ : 0 < J) : stoppingRho J J = 0 := by
  simp [stoppingRho, (Nat.cast_pos.mpr hJ : (0 : ℝ) < J).ne']

/--
@isnad1 id=eq.0h2v.s5.80aaf647c0f8 from=translated src=- shape=bd682630 vocab=baa93f7a
-/
theorem stoppingRho_succ (J i : ℕ) :
    stoppingRho J (i + 1) = stoppingRho J i - 100 / J := by
  simp only [stoppingRho, Nat.cast_add, Nat.cast_one]
  ring

/--
@isnad1 id=le.2h2v.s5.5b37fe914ec0 from=translated src=- shape=13720033 vocab=81413bcf
-/
theorem stoppingRho_nonneg {J i : ℕ} (hJ : 0 < J) (hi : i ≤ J) : 0 ≤ stoppingRho J i := by
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr
    ((div_le_one (Nat.cast_pos.mpr hJ : (0 : ℝ) < J)).mpr (Nat.cast_le.mpr hi)))

/--
@isnad1 id=eq.0h2v.s6.c92dc6ddd84e from=translated src=- shape=e2a46da4 vocab=69712be0
-/
theorem stoppingAlpha_succ (J i : ℕ) :
    stoppingAlpha J (i + 1) = stoppingAlpha J i + 1 / (J : ℝ) ^ 2 := by
  simp only [stoppingAlpha, Nat.cast_add, Nat.cast_one]
  ring

/--
@isnad1 id=lt.1h2v.s4.87f2dca3a5ee from=translated src=- shape=c8a788b1 vocab=623e707c
-/
theorem stoppingAlpha_pos {J : ℕ} (hJ : 0 < J) (i : ℕ) : 0 < stoppingAlpha J i := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  unfold stoppingAlpha
  positivity

/--
@isnad1 id=le.2h2v.s5.6a43a6a83d28 from=translated src=- shape=40207d33 vocab=a065cb0f
-/
theorem stoppingAlpha_le_two_div {J i : ℕ} (hJ : 0 < J) (hi : i ≤ J) :
    stoppingAlpha J i ≤ 2 / J := by
  have hJ' : (J : ℝ) ≠ 0 := (Nat.cast_pos.mpr hJ : (0 : ℝ) < J).ne'
  calc
    _ ≤ 1 / J + (J : ℝ) / (J : ℝ) ^ 2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right (Nat.cast_le.mpr hi) (sq_nonneg _))
    _ = _ := by field_simp; ring

/--
@isnad1 id=eq.1h3v.s6.3db84e664289 from=translated src=- shape=ef315962 vocab=3dbfa697
-/
theorem stopping_density_mul_image {V N ρ : ℝ} (hN : 0 < N) :
    (V * N ^ (-2 + ρ)) * N ^ (2 - ρ) = V := by
  rw [mul_assoc, ← Real.rpow_add hN, show (-2 + ρ) + (2 - ρ) = 0 by ring,
    Real.rpow_zero, mul_one]

/--
@isnad1 id=eq.1h4v.s7.88ef3a44a6dc from=translated src=- shape=8cee59fe vocab=0d6817ba
-/
theorem inner_threshold_mul_image {V N : ℝ} (hN : 0 < N) (J i : ℕ) :
    (V * N ^ (-2 + stoppingRho J i - 200 / J)) *
      N ^ (2 - stoppingRho J (i + 1)) = V * N ^ (-100 / (J : ℝ)) := by
  rw [stoppingRho_succ, mul_assoc, ← Real.rpow_add hN]
  congr 2
  ring

/--
@isnad1 id=eq.1h3v.s6.c2da42c6d2cf from=translated src=- shape=9c747721 vocab=4026cd86
-/
theorem stopping_loss_gap {N : ℝ} (hN : 0 < N) (J i : ℕ) :
    N ^ (-stoppingAlpha J (i + 1)) * N ^ (1 / (J : ℝ) ^ 2) =
      N ^ (-stoppingAlpha J i) := by
  rw [← Real.rpow_add hN, stoppingAlpha_succ]
  congr 1
  ring

/--
@isnad1 id=le.3h3v.s6.6ba217c6bc54 from=translated src=- shape=975a3d9a vocab=b1c30cb5
-/
theorem density_cut_loss_le_child_loss {N : ℝ} (hN : 1 ≤ N)
    {J i : ℕ} (hJ : 0 < J) (hi : i < J) :
    N ^ (-100 / (J : ℝ)) ≤ N ^ (-stoppingAlpha J (i + 1)) := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  have ha := stoppingAlpha_le_two_div hJ (Nat.succ_le_of_lt hi)
  change stoppingAlpha J (i + 1) ≤ 2 / J at ha
  have hd : (2 : ℝ) / J ≤ 100 / J :=
    div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg J)
  simpa only [neg_div] using neg_le_neg (ha.trans hd)

/-- The exact large-projection condition that pays for all three child refinements.
@isnad1 id=le.7h6v.s8.3ce8851a6dbe from=translated src=- shape=bc1d62ef vocab=80208566
-/
theorem child_pruning_budget {N V r k : ℝ} (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hr : 0 ≤ r) (hk : 0 ≤ k) {J i : ℕ} (hJ : 0 < J) (hi : i < J)
    (hlarge : 4 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2)) :
    (1 + 2 * k) * (r * (V * N ^ (-stoppingAlpha J (i + 1))) +
      r * (V * N ^ (-100 / (J : ℝ)))) ≤ V * N ^ (-stoppingAlpha J i) / 2 := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hcut := density_cut_loss_le_child_loss hN hJ hi
  have hcoeff : 2 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2) / 2 := by linarith
  calc
    _ ≤ (1 + 2 * k) * (r * (V * N ^ (-stoppingAlpha J (i + 1))) +
        r * (V * N ^ (-stoppingAlpha J (i + 1)))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcut hV) hr)) (by positivity)
    _ = (2 * (1 + 2 * k) * r) * (V * N ^ (-stoppingAlpha J (i + 1))) := by ring
    _ ≤ (N ^ (1 / (J : ℝ) ^ 2) / 2) * (V * N ^ (-stoppingAlpha J (i + 1))) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hV (Real.rpow_nonneg hNpos.le _))
    _ = V * (N ^ (-stoppingAlpha J (i + 1)) * N ^ (1 / (J : ℝ) ^ 2)) / 2 := by ring
    _ = _ := by rw [stopping_loss_gap hNpos]

/--
@isnad1 id=le.2h4v.s7.db7e37f0c591 from=translated src=- shape=035d557b vocab=615faa1f
-/
theorem child_pruning_threshold {r k N : ℝ} {J : ℕ} (hJ : 0 < J)
    (hN : (max 1 (4 * (1 + 2 * k) * r)) ^ (J : ℝ) ^ 2 ≤ N) :
    4 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2) := by
  let B := max 1 (4 * (1 + 2 * k) * r)
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hJpos : (0 : ℝ) < (J : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hJ)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le _) hN
    (div_nonneg zero_le_one hJpos.le)
  rw [one_div, Real.rpow_rpow_inv hBpos.le hJpos.ne'] at hpow
  have hLB : 4 * (1 + 2 * k) * r ≤ B := le_max_right _ _
  simpa only [one_div] using hLB.trans hpow

/--
@isnad1 id=ex.1h3v.s7.ad1e508b819c from=translated src=- shape=82f4af9f vocab=341180a7
-/
theorem exists_child_pruning_threshold (r k : ℝ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N, N₀ ≤ N →
      4 * (1 + 2 * k) * r ≤ N ^ (1 / (J : ℝ) ^ 2) :=
  ⟨(max 1 (4 * (1 + 2 * k) * r)) ^ (J : ℝ) ^ 2,
    Real.one_le_rpow (le_max_left _ _) (sq_nonneg _), fun _ hN ↦
      child_pruning_threshold hJ hN⟩

end NKBesicovitch.Projection
