/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Dilation
public import Tengoku.Seed.MeasureTheory.Group.Pointwise
public import Tengoku.Seed.Analysis.Normed.Module.Ball.Pointwise

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restoring the general multiplicity factor

For positive line mass, parallel multiplicity is positive and finite.
Dilate space by the positive `m`th root of its reciprocal. The normalized
family has multiplicity one, and its projection-size bound is `N/M ≥ 1`.
Undoing the dilation recovers `L ≤ C M^(2-β) N^β` with the same constant.
The zero-mass case is handled before taking any reciprocal.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal Pointwise

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=le.3h5v.s7.cd8b40d21a75 from=translated src=- shape=21609280 vocab=72bdf000
-/
theorem restore_multiplicity {L M N C β : ℝ} (hM : 0 < M) (hN : 0 ≤ N)
    (h : (M⁻¹) ^ 2 * L ≤ C * (N / M) ^ β) :
    L ≤ C * M ^ (2 - β) * N ^ β := by
  calc
    L = M ^ 2 * ((M⁻¹) ^ 2 * L) := by field_simp
    _ ≤ M ^ 2 * (C * (N / M) ^ β) := mul_le_mul_of_nonneg_left h (sq_nonneg M)
    _ = _ := by
      rw [Real.div_rpow hN hM.le, Real.rpow_sub hM, Real.rpow_two]
      ring

/--
@isnad1 id=le.5h5v.s10.bd7c853cd205 from=translated src=- shape=b583e816 vocab=20465f4a
-/
theorem volume_le_of_normalized [Nonempty (Fin m)] {β C : ℝ}
    {Γ : Finset ℝ} (hΓ : Γ.Nonempty) (hC : 0 ≤ C)
    (hbound : ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (parallelMultiplicity G).toReal ≤ 1 →
      ∀ N : ℝ, 1 ≤ N → (∀ t ∈ Γ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      (volume G).toReal ≤ C * N ^ β)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G) :
    (volume G).toReal ≤ C * (parallelMultiplicity G).toReal ^ (2 - β) *
      (sliceSize Γ G).toReal ^ β := by
  by_cases hzero : volume G = 0
  · rw [hzero, ENNReal.toReal_zero]
    positivity
  let M := (parallelMultiplicity G).toReal
  let N := (sliceSize Γ G).toReal
  have hM : 0 < M := ENNReal.toReal_pos
    (parallelMultiplicity_pos hG (pos_iff_ne_zero.mpr hzero)).ne' (parallelMultiplicity_ne_top hGb)
  have hNfin := sliceSize_ne_top Γ hGb
  have hMN : M ≤ N := by
    obtain ⟨t, ht⟩ := hΓ
    exact ENNReal.toReal_mono hNfin ((parallelMultiplicity_le_projection G t).trans
      (volume_projection_le_sliceSize ht G))
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos_iff_nonempty.mpr inferInstance).ne'
  let r := (M⁻¹) ^ (m : ℝ)⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (inv_pos.mpr hM) _
  have hrm : r ^ m = M⁻¹ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_inv_rpow (inv_nonneg.mpr hM.le) hm
  have hFM : (parallelMultiplicity (r • G)).toReal ≤ 1 := by
    rw [parallelMultiplicity_smul hr, ENNReal.toReal_mul, hrm,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hM.le)]
    exact (inv_mul_cancel₀ hM.ne').le
  have hπ (t : ℝ) (ht : t ∈ Γ) :
      volume (atHeight t '' (r • G)) ≤ ENNReal.ofReal (N / M) := by
    rw [volume_projection_smul t hr.le, hrm]
    calc
      _ ≤ ENNReal.ofReal M⁻¹ * sliceSize Γ G :=
        mul_le_mul le_rfl (volume_projection_le_sliceSize ht G) bot_le bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_toReal hNfin, ← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
        congr 1
        exact mul_comm _ _
  have h := hbound (r • G) (hG.const_smul_of_ne_zero hr.ne') (hGb.smul₀ r) hFM
    (N / M) ((one_le_div hM).mpr hMN) hπ
  rw [volume_lineFamily_smul hr.le, ENNReal.toReal_mul, hrm,
    ENNReal.toReal_ofReal (sq_nonneg _)] at h
  exact restore_multiplicity hM hN h

/--
@isnad1 id=hasproje.3h4v.s10.4a9356ea9699 from=translated src=- shape=45837685 vocab=9c28f8b7
-/
theorem hasProjectionEstimate_of_normalized [Nonempty (Fin m)] {β C : ℝ}
    {Γ : Finset ℝ} (hΓ : Γ.Nonempty) (hC : 0 < C)
    (hbound : ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (parallelMultiplicity G).toReal ≤ 1 →
      ∀ N : ℝ, 1 ≤ N → (∀ t ∈ Γ, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      (volume G).toReal ≤ C * N ^ β) : HasProjectionEstimate m β Γ :=
  ⟨C, hC, fun _ hG hGb ↦ volume_le_of_normalized hΓ hC.le hbound hG hGb⟩

end NKBesicovitch.Projection
