/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Circuits.KarchmerWigderson.TopDown.Defs
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.MirrorSets
public import Tengoku.Complexitylib.Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Sampling
public import Tengoku

/-!
# Maintaining the density rectangle through one message

A weighted pigeonhole argument bounds the entropy loss of a message cell.
Use the improved mirror set when the existing limit condition faces the wrong
speaker. A density limit at rate below `3/4` precludes a fixed separating coordinate.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsDensityLimit.agrees_internal {Y : Finset (ι → Bool)} {p k : ℝ} {x : ι → Bool}
    (hlim : IsDensityLimit Y p k x) (hp : 0 ≤ p) (hp' : p < 3 / 4) (i : ι) :
    ∃ y ∈ Y, y i = x i := by
  by_contra hn
  have hd (P : ι → Bool) (hi : P i ≠ true) : coordinateDensity Y P x = 0 := by
    rw [coordinateDensity_eq_expect]
    apply expect_eq_zero
    intro y _
    have hy : resample P x y ∉ Y := by
      intro hy
      apply hn
      exact ⟨resample P x y, hy, by simp [resample, hi]⟩
    simp [hy]
  have hpoint (P : ι → Bool) :
      (if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0) ≤
        if P i then 1 else 0 := by
    by_cases hi : P i = true
    · rw [ite_eq_left hi]
      split_ifs <;> norm_num
    · rw [ite_eq_right hi, hd P hi]
      have hn : ¬ (2 : ℝ) ^ (-k) ≤ 0 := not_le.mpr (by positivity)
      rw [ite_eq_right hn]
  have h := bernoulliAverage_mono hp (show p ≤ 1 by linarith) hpoint
  rw [bernoulliAverage_coordinate_internal] at h
  unfold IsDensityLimit at hlim
  linarith

theorem IsDensityLimit.mono_deficit_internal {Y : Finset (ι → Bool)} {p k k' : ℝ} {x : ι → Bool}
    (hlim : IsDensityLimit Y p k x) (hp : 0 ≤ p) (hp' : p ≤ 1) (hkk' : k ≤ k') :
    IsDensityLimit Y p k' x := by
  refine hlim.trans (bernoulliAverage_mono hp hp' fun P => ?_)
  by_cases h : (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x
  · have h' : (2 : ℝ) ^ (-k') ≤ coordinateDensity Y P x :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hkk')).trans h
    simp only [ite_eq_left h, ite_eq_left h', le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

end Complexity.BooleanAnalysis

namespace Complexity.KarchmerWigderson

open BooleanAnalysis Finset
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem DensityRectangle.swap_internal {X Y : Finset (ι → Bool)} {p k : ℝ}
    (h : DensityRectangle X Y p k) : DensityRectangle Y X p k := by
  rcases h with ⟨hX, hY, hdX, hdY, r, hr, hrp, hl | hl⟩
  · exact ⟨hY, hX, hdY, hdX, r, hr, hrp, Or.inr hl⟩
  · exact ⟨hY, hX, hdY, hdX, r, hr, hrp, Or.inl hl⟩

theorem DensityRectangle.not_separated_internal {X Y : Finset (ι → Bool)} {p k : ℝ}
    (h : DensityRectangle X Y p k) (hp : p < 3 / 4) (i : ι) :
    ¬ ∀ x ∈ X, ∀ y ∈ Y, x i ≠ y i := by
  intro hsep
  rcases h with ⟨hX, hY, _, _, r, hr, hrp, hl | hl⟩
  · obtain ⟨x, hx⟩ := hX
    obtain ⟨y, hy, he⟩ := (hl x hx).agrees_internal hr.le (hrp.trans_lt hp) i
    exact hsep x hx y hy he.symm
  · obtain ⟨y, hy⟩ := hY
    obtain ⟨x, hx, he⟩ := (hl y hy).agrees_internal hr.le (hrp.trans_lt hp) i
    exact hsep x hx y hy he

end Complexity.KarchmerWigderson
