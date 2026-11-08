/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
public import Tengoku.Seed.Analysis.RCLike.Basic
public import Tengoku.Seed.Data.Complex.Basic
public import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral parametrisations

This file defines explicit complex-valued parametrisations used to rewrite contour integrals in
the magic function argument.

## Main definitions
* `MagicFunction.Parametrisations.z₁`, `MagicFunction.Parametrisations.z₂`,
  `MagicFunction.Parametrisations.z₃`, `MagicFunction.Parametrisations.z₄`,
  `MagicFunction.Parametrisations.z₅`, `MagicFunction.Parametrisations.z₆`
* Their extensions `z₁'`--`z₆'` to all real parameters.
-/

namespace MagicFunction.Parametrisations

open Set Complex Real

local notation "ℍ₀" => UpperHalfPlane.upperHalfPlaneSet

noncomputable section Parametrisations

/-- Parametrisation `t ↦ -1 + i t` of the vertical segment from `-1` to `-1 + i`.-/
@[expose] public def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 + I * t

/-- Extension of `z₁` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.-/
@[expose] public def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t

/-- Parametrisation `t ↦ -1 + t + i` of the horizontal segment from `-1 + i` to `i`.-/
@[expose] public def z₂ (t : Icc (0 : ℝ) 1) : ℂ := -1 + t + I

/-- Extension of `z₂` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.-/
@[expose] public def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t

/-- Parametrisation `t ↦ 1 + i t` of the vertical segment from `1` to `1 + i`.-/
@[expose] public def z₃ (t : Icc (0 : ℝ) 1) : ℂ := 1 + I * t

/-- Extension of `z₃` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.-/
@[expose] public def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t

/-- Parametrisation `t ↦ 1 - t + i` of the horizontal segment from `1 + i` to `i`.-/
@[expose] public def z₄ (t : Icc (0 : ℝ) 1) : ℂ := 1 - t + I

/-- Extension of `z₄` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.-/
@[expose] public def z₄' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₄ t

/-- Parametrisation `t ↦ i t` of the vertical segment from `0` to `i`.-/
@[expose] public def z₅ (t : Icc (0 : ℝ) 1) : ℂ := I * t

/-- Extension of `z₅` to a map `ℝ → ℂ` via `IccExtend`.

The prime indicates we have extended a parametrisation on `Icc (0, 1)` to all real `t`.-/
@[expose] public def z₅' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₅ t

/-- Parametrisation `t ↦ i t` of the ray `i * Ici 1`.-/
@[expose] public def z₆ (t : Ici (1 : ℝ)) : ℂ := I * t

/-- Extension of `z₆` to a map `ℝ → ℂ` via `IciExtend`.

The prime indicates we have extended a parametrisation on `Ici 1` to all real `t`.-/
@[expose] public def z₆' (t : ℝ) : ℂ := IciExtend z₆ t

/-- The imaginary part of `z₂'` is always positive (in fact, it is equal to `1`).-/
public lemma im_z₂'_pos_all (t : ℝ) : 0 < (z₂' t).im := by
  simp [z₂', Set.IccExtend_apply, z₂]

/-- The imaginary part of `z₄'` is always positive (in fact, it is equal to `1`).-/
public lemma im_z₄'_pos_all (t : ℝ) : 0 < (z₄' t).im := by
  simp [z₄', Set.IccExtend_apply, z₄]

/-- The extended parametrisation `z₅'` stays in the closed unit disk.-/
public lemma norm_z₅'_le_one (t : ℝ) : ‖z₅' t‖ ≤ 1 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu1 : u ≤ 1 := by simp [hu]
  have hnorm : ‖z₅' t‖ = u := by
    simp [z₅', Set.IccExtend_apply, z₅, hu, Complex.norm_real]
  simpa [hnorm] using hu1

/-- The extended parametrisation `z₁'` stays in the closed ball of radius `2` centered at `0`.-/
public lemma norm_z₁'_le_two (t : ℝ) : ‖z₁' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu0 : 0 ≤ u := by simp [hu]
  have hu1 : u ≤ 1 := by simp [hu]
  have huabs : |u| ≤ 1 := by
    simpa [abs_of_nonneg hu0] using hu1
  have hz : z₁' t = (-1 : ℂ) + (I : ℂ) * (u : ℂ) := by
    simp [z₁', Set.IccExtend_apply, z₁, hu]
  calc
    ‖z₁' t‖ = ‖(-1 : ℂ) + (I : ℂ) * (u : ℂ)‖ := by simp [hz]
    _ ≤ ‖(-1 : ℂ)‖ + ‖(I : ℂ) * (u : ℂ)‖ := norm_add_le _ _
    _ = (1 : ℝ) + ‖(u : ℂ)‖ := by simp
    _ = 1 + |u| := by simp [Complex.norm_real]
    _ ≤ 1 + 1 := by
          simpa [add_comm] using add_le_add_right huabs 1
    _ = 2 := by ring

/-- The extended parametrisation `z₂'` stays in the closed ball of radius `2` centered at `0`.-/
public lemma norm_z₂'_le_two (t : ℝ) : ‖z₂' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu0 : 0 ≤ u := by simp [hu]
  have hu1 : u ≤ 1 := by simp [hu]
  have habs : |u - 1| ≤ 1 := by
    grind only [= max_def, = min_def, = abs.eq_1]
  have hnorm : ‖(-1 : ℂ) + (u : ℂ)‖ ≤ 1 := by
    have : ‖(-1 : ℂ) + (u : ℂ)‖ = |u - 1| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Complex.norm_real (u - 1))
    simpa [this] using habs
  have hz : z₂' t = ((-1 : ℂ) + (u : ℂ)) + (I : ℂ) := by
    simp [z₂', Set.IccExtend_apply, z₂, hu]
  calc
    ‖z₂' t‖ = ‖((-1 : ℂ) + (u : ℂ)) + (I : ℂ)‖ := by simp [hz]
    _ ≤ ‖(-1 : ℂ) + (u : ℂ)‖ + ‖(I : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 : ℝ) + 1 := add_le_add hnorm (by simp)
    _ = 2 := by ring

/-- The extended parametrisation `z₄'` stays in the closed ball of radius `2` centered at `0`.-/
public lemma norm_z₄'_le_two (t : ℝ) : ‖z₄' t‖ ≤ 2 := by
  set u : ℝ := max 0 (min 1 t) with hu
  have hu0 : 0 ≤ u := by simp [hu]
  have hu1 : u ≤ 1 := by simp [hu]
  have habs : |1 - u| ≤ 1 := by
    have hle : 0 ≤ 1 - u := sub_nonneg.mpr hu1
    have habs_eq : |1 - u| = 1 - u := abs_of_nonneg hle
    simpa [habs_eq] using sub_le_self (1 : ℝ) hu0
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ ≤ 1 := by
    have : ‖(1 : ℂ) - (u : ℂ)‖ = |1 - u| := by
      simpa using Complex.norm_real (1 - u)
    simpa [this] using habs
  have hz : z₄' t = ((1 : ℂ) - (u : ℂ)) + (I : ℂ) := by
    simp [z₄', Set.IccExtend_apply, z₄, hu, sub_eq_add_neg]
  calc
    ‖z₄' t‖ = ‖((1 : ℂ) - (u : ℂ)) + (I : ℂ)‖ := by simp [hz]
    _ ≤ ‖(1 : ℂ) - (u : ℂ)‖ + ‖(I : ℂ)‖ := norm_add_le _ _
    _ ≤ (1 : ℝ) + 1 := add_le_add hnorm (by simp)
    _ = 2 := by ring

end Parametrisations

section UpperHalfPlane

open scoped UpperHalfPlane

private lemma im_pos_of_mapsto {s : Set ℝ} {f : ℝ → ℂ} (hf : MapsTo f s ℍ₀) {t : ℝ} (ht : t ∈ s) :
    0 < (f t).im := by
  simpa [UpperHalfPlane.upperHalfPlaneSet] using hf ht

end UpperHalfPlane

section eq_of_mem

/-- On `Icc 0 1`, the extension `z₁'` agrees with the original parametrisation `z₁`.-/
public lemma z₁'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₁' t = -1 + I * t := by
  rw [z₁', IccExtend_of_mem zero_le_one z₁ ht, z₁]

/-- On `Icc 0 1`, the extension `z₃'` agrees with the original parametrisation `z₃`.-/
public lemma z₃'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = 1 + I * t := by
  rw [z₃', IccExtend_of_mem zero_le_one z₃ ht, z₃]

/-- On `Icc 0 1`, the extension `z₅'` agrees with the original parametrisation `z₅`.-/
public lemma z₅'_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 1) : z₅' t = I * t := by
  rw [z₅', IccExtend_of_mem zero_le_one z₅ ht, z₅]

/-- On `Ici 1`, the extension `z₆'` agrees with the original parametrisation `z₆`.-/
public lemma z₆'_eq_of_mem {t : ℝ} (ht : t ∈ Ici 1) : z₆' t = I * t := by
  rw [z₆', IciExtend_of_mem z₆ ht, z₆]

/-- On `Icc 0 1`, the points `z₃' t` and `z₅' t` differ by the translation `+ 1`.-/
public lemma z₃'_eq_z₅'_add_one {t : ℝ} (ht : t ∈ Icc 0 1) : z₃' t = z₅' t + 1 := by
  simp [z₃'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht, add_comm]

end eq_of_mem

end MagicFunction.Parametrisations
