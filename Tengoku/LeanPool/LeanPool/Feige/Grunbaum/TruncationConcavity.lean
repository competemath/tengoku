/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.Definitions
import Tengoku.LeanPool.LeanPool.Isoperimetric.BrunnMinkowski
public import Tengoku

/-!
# Concavity of truncated-volume roots
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace Grunbaum

/-- The part of `C` cut out by the sublevel halfspace of `ℓ` at `t`. -/
def trunc {d : ℕ} (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : Set (Euc d) :=
  C ∩ ℓ ⁻¹' Set.Iic t

/-- The dimension-normalized root of a truncation's volume. -/
noncomputable def truncRoot {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  (volume (trunc C ℓ t) ^ ((d : ℝ) + 1)⁻¹).toReal

/-- The dimension-normalized root of the truncation's volume ratio. -/
noncomputable def cdfRoot {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  ((volume (trunc C ℓ t) / volume C) ^ ((d : ℝ) + 1)⁻¹).toReal

/-- Thresholds for which the corresponding truncation is nonempty. -/
def truncDomain {d : ℕ} (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) : Set ℝ :=
  {t | (trunc C ℓ t).Nonempty}

lemma isCompact_trunc {d : ℕ} {C : Set (Euc d)} (hC : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    IsCompact (trunc C ℓ t) :=
  hC.inter_right (isClosed_Iic.preimage ℓ.continuous)

lemma volume_trunc_ne_top {d : ℕ} {C : Set (Euc d)} (hC : IsCompact C)
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    volume (trunc C ℓ t) ≠ ⊤ :=
  (isCompact_trunc hC ℓ t).measure_lt_top.ne

private lemma weighted_trunc_subset {d : ℕ} {C : Set (Euc d)}
    (hC : Convex ℝ C) (ℓ : Euc d →L[ℝ] ℝ)
    {s t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • trunc C ℓ s + b • trunc C ℓ t ⊆ trunc C ℓ (a * s + b * t) := by
  rintro z ⟨ax, ⟨x, hx, rfl⟩, by_, ⟨y, hy, rfl⟩, rfl⟩
  change x ∈ C ∧ ℓ x ≤ s at hx
  change y ∈ C ∧ ℓ y ≤ t at hy
  refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
  change ℓ (a • x + b • y) ≤ a * s + b * t
  simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
    (mul_le_mul_of_nonneg_left hy.2 hb)

theorem convex_truncDomain {d : ℕ} {C : Set (Euc d)}
    (hCconv : Convex ℝ C) (ℓ : Euc d →L[ℝ] ℝ) :
    Convex ℝ (truncDomain C ℓ) := by
  intro s hs t ht a b ha hb hab
  change (trunc C ℓ s).Nonempty at hs
  change (trunc C ℓ t).Nonempty at ht
  change (trunc C ℓ (a * s + b * t)).Nonempty
  rcases hs with ⟨x, hx⟩
  rcases ht with ⟨y, hy⟩
  exact ⟨a • x + b • y,
    weighted_trunc_subset hCconv ℓ ha hb hab
      (add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy))⟩

lemma cdfRoot_eq {d : ℕ} (C : Set (Euc d))
    (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) :
    cdfRoot C ℓ t =
      (volume C ^ ((d : ℝ) + 1)⁻¹).toReal⁻¹ * truncRoot C ℓ t := by
  unfold cdfRoot truncRoot
  rw [ENNReal.div_rpow_of_nonneg _ _ (by positivity), ENNReal.toReal_div]
  simp only [div_eq_mul_inv, mul_comm]

end Grunbaum
