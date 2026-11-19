/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/
/-
Vendored from `Vilin97/lean-pool` revision
`9c296f447f48f3242df5e65e0b6120ddffcd79a7`, file
`LeanPool/Isoperimetric/BrunnMinkowski.lean`.
-/
import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
import Tengoku.MahlerHansenCograph.Formalisation.Mathlib.Analysis.Convex.PrekopaLeindler

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Brunn–Minkowski inequality

This file deduces the Brunn–Minkowski inequality from the Prékopa–Leindler
inequality, both for the standard product measure on `ℝⁿ` and for the
Euclidean structure `EuclideanSpace ℝ (Fin n)`.
-/
namespace Tengoku.MahlerHansenCograph end Tengoku.MahlerHansenCograph open Tengoku.MahlerHansenCograph
open MeasureTheory Set
open scoped Pointwise

/-- Brunn–Minkowski when `A` has infinite volume.
@isnad1 id=le.3h4v.s10.fe0acea58880 from=translated src=- shape=1e556bd9 vocab=f3e3004d
-/
lemma _root_.Tengoku.MahlerHansenCograph.brunn_minkowski_infinite
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA : volume A = ⊤) (hB : B.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_top_pow : (⊤ : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = ⊤ :=
    ENNReal.top_rpow_of_pos Nat.inv_pos_of_nat
  calc
    (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ =
        (volume (A + {hB.some}))^((d:ℝ)+1)⁻¹ := by
      simp [hA, h_top_pow]
    _ ≤ (volume (A + B))^((d:ℝ)+1)⁻¹ := by gcongr; exact singleton_subset_iff.mpr hB.some_mem
    _ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by gcongr

/-- Brunn–Minkowski when `A` has zero volume.
@isnad1 id=le.3h4v.s10.6f59659841fc from=translated src=- shape=68d010c4 vocab=070e6bc8
-/
lemma _root_.Tengoku.MahlerHansenCograph.brunn_minkowski_zero
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA_zero : volume A = 0) (hA_nonempty : A.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_zero_pow : (0 : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = 0 :=
    ENNReal.zero_rpow_of_pos Nat.inv_pos_of_nat
  simp only [hA_zero, h_zero_pow, zero_add]
  gcongr 1
  calc
    volume B = volume ({hA_nonempty.some} + B) := by simp
    _ ≤ volume (A + B) := by gcongr; exact singleton_subset_iff.mpr hA_nonempty.some_mem
    _ ≤ volume C := by gcongr

/-- Prékopa–Leindler applied to indicator functions of two measurable sets.
@isnad1 id=le.5h4v.s10.8e4d7aa47481 from=translated src=- shape=f25b0b0b vocab=1cf7b7b5
-/
lemma _root_.Tengoku.MahlerHansenCograph.prekopa_leindler_indicator
    {d : ℕ} {θ : ℝ} {A B : Set (Fin (d + 1) → ℝ)}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hA_measurable : MeasurableSet A) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * volume A^(1-θ) * volume B^θ ≤ volume (A + B) := by
  have : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ x, (A.indicator fun _ ↦ (1 : ENNReal)) x)^(1-θ)
      * (∫⁻ x, (B.indicator fun _ ↦ (1 : ENNReal)) x)^θ
      ≤ ∫⁻ x, ((A + B).indicator fun _ ↦ (1 : ENNReal)) x := prekopa_leindler ⟨
    hθ0, hθ1, by measurability, by measurability, by measurability, by
    show ∀ (x y : Fin (d + 1) → ℝ),
      ((A.indicator fun _ ↦ (1 : ENNReal)) x) ^ (1 - θ)
      * ((B.indicator fun _ ↦ (1 : ENNReal)) y) ^ θ
      ≤ ((A + B).indicator fun _ ↦ (1 : ENNReal)) (x + y)
    intro x y
    unfold indicator
    simp_all only [ite_pow, ENNReal.one_rpow, sub_pos, ENNReal.zero_rpow_of_pos, mul_ite, mul_one,
      mul_zero]
    split
    · split
      · split
        · rfl
        · expose_names; exact False.elim (h_2 (add_mem_add h_1 h))
      · simp only [zero_le]
    simp only [zero_le]⟩
  simp_all  -- Rewrite the integrals of indicators as volumes

/-- The Brunn–Minkowski inequality in arbitrary dimension.
@isnad1 id=le.5h3v.s10.2fae9ec487b8 from=translated src=- shape=a0aad12f vocab=9baf911e
-/
theorem _root_.Tengoku.MahlerHansenCograph.brunn_minkowski
    {d : ℕ} {A B : Set (Fin (d + 1) → ℝ)}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : volume A ^ ((d:ℝ)+1)⁻¹ + volume B ^ ((d:ℝ)+1)⁻¹ ≤ volume (A + B) ^ ((d:ℝ)+1)⁻¹ := by
  -- Handle the cases of 0 volume or infinite volume
  have hAB : A + B ⊆ A + B := by rfl
  by_cases hvolAinf : volume A = ⊤
  · exact brunn_minkowski_infinite hvolAinf hB_nonempty hAB
  by_cases hvolAzero : volume A = 0
  · exact brunn_minkowski_zero hvolAzero hA_nonempty hAB
  by_cases hvolBinf : volume B = ⊤
  · rw [add_comm]; nth_rw 1 [add_comm A B] at hAB
    exact brunn_minkowski_infinite hvolBinf hA_nonempty hAB
  by_cases hvolBzero : volume B = 0
  · rw [add_comm]; nth_rw 1 [add_comm A B] at hAB
    exact brunn_minkowski_zero hvolBzero hB_nonempty hAB
  -- Apply Prekopa-Leindler to the indicator functions for A, B, and A + B
  let f : (Fin (d + 1) → ℝ) → ENNReal := A.indicator fun _ ↦ 1
  let g : (Fin (d + 1) → ℝ) → ENNReal := B.indicator fun _ ↦ 1
  let h : (Fin (d + 1) → ℝ) → ENNReal := (A + B).indicator fun _ ↦ 1
  let D : ℝ := d + 1
  let va : ℝ := (volume A).toReal^D⁻¹
  let vb : ℝ := (volume B).toReal^D⁻¹
  let θ : ℝ := vb * (va + vb)⁻¹
  have h_va_pos : 0 < va := Real.rpow_pos_of_pos (ENNReal.toReal_pos hvolAzero hvolAinf) _
  have h_vb_pos : 0 < vb := Real.rpow_pos_of_pos (ENNReal.toReal_pos hvolBzero hvolBinf) _
  have h_va_plus_vb_pos : 0 < va + vb := by linarith
  -- We have θ ∈ (0, 1) since A and B both have nonzero and non-infinite volume.
  have hθ0 : 0 < θ := div_pos h_vb_pos (add_pos' h_va_pos h_vb_pos)
  have hθ1 : θ < 1 := (mul_inv_lt_iff₀ h_va_plus_vb_pos).mpr (by linarith)
  have h_result : ENNReal.ofReal ((1-θ)^(D*(1-θ))*θ^(D*θ))⁻¹
      * volume A^(1-θ) * volume B^θ ≤ volume (A + B) :=
    prekopa_leindler_indicator hθ0 hθ1 hA_measurable hB_measurable hAB_measurable
  -- Raise both sides to the 1/D power
  have h_result_simp : ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ)⁻¹
      * (volume A^(1-θ))^D⁻¹ * (volume B^θ)^D⁻¹ ≤ volume (A + B)^D⁻¹ := by
    have h_D_θ_expr_pos : 0 < (1-θ)^(D*(1-θ))*θ^(D*θ) :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hθ0 _)
    have h_Dinv_nonneg : 0 ≤ D⁻¹ := Nat.inv_pos_of_nat.le
    rw [← ENNReal.rpow_le_rpow_iff Nat.inv_pos_of_nat,
      ENNReal.mul_rpow_of_nonneg _ _ h_Dinv_nonneg,
      ENNReal.mul_rpow_of_nonneg _ _ h_Dinv_nonneg,
      ENNReal.ofReal_rpow_of_pos (by rw [inv_pos]; exact h_D_θ_expr_pos)] at h_result
    have : ((1-θ)^(D*(1-θ))*θ^(D*θ))⁻¹^D⁻¹ = ((1-θ)^(1-θ)*θ^θ)⁻¹ := by
      rw [Real.inv_rpow (le_of_lt h_D_θ_expr_pos),
        Real.mul_rpow
          (Real.rpow_nonneg (by linarith) (D * (1 - θ))) (Real.rpow_nonneg (le_of_lt hθ0) (D * θ)),
        ← Real.rpow_mul (by linarith), ← Real.rpow_mul (le_of_lt hθ0)]
      congr 3
      · grind
      grind
    rw [this] at h_result
    exact h_result
  -- Simplify to get the desired result
  have h_result_simp_2 : ENNReal.ofReal (va + vb) ≤ volume (A + B) ^ D⁻¹ := by
    have h_cancel_D : D⁻¹ * D = 1 := by unfold D; field_simp
    have hva : volume A = (ENNReal.ofReal va)^D := by
      rw [ENNReal.ofReal_rpow_of_pos h_va_pos, ← Real.rpow_mul ENNReal.toReal_nonneg]
      simp [h_cancel_D, hvolAinf]
    have hvb : volume B = (ENNReal.ofReal vb)^D := by
      rw [ENNReal.ofReal_rpow_of_pos h_vb_pos, ← Real.rpow_mul ENNReal.toReal_nonneg]
      simp [h_cancel_D, hvolBinf]
    have h_va_vb : 1 - vb * (va + vb)⁻¹ = va * (va + vb)⁻¹ := by grind
    have h_vapvb_inv_pos: 0 < (va + vb)⁻¹ := inv_pos.mpr h_va_plus_vb_pos
    have h_expr_nonneg : 0 ≤
        ((va*(va + vb)⁻¹)^(va*(va + vb)⁻¹) * (vb*(va + vb)⁻¹)^(vb*(va + vb)⁻¹))⁻¹ := by
      rw [inv_nonneg]
      exact mul_nonneg
        (Real.rpow_nonneg
          (mul_nonneg (le_of_lt h_va_pos) (le_of_lt h_vapvb_inv_pos)) (va * (va + vb)⁻¹))
        (Real.rpow_nonneg
          (mul_nonneg (le_of_lt h_vb_pos) (le_of_lt h_vapvb_inv_pos)) (vb * (va + vb)⁻¹))
    have h_expr_2_nonneg : 0 ≤
        ((va*(va + vb)⁻¹)^(va*(va + vb)⁻¹) * (vb*(va + vb)⁻¹)^(vb*(va + vb)⁻¹))⁻¹
        * ((va^D)^(va*(va + vb)⁻¹))^D⁻¹ := by
      apply mul_nonneg h_expr_nonneg
      apply Real.rpow_nonneg; apply Real.rpow_nonneg; apply Real.rpow_nonneg (le_of_lt h_va_pos)
    rw [hva, hvb, h_va_vb,
      ENNReal.ofReal_rpow_of_pos h_va_pos,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h_va_pos D),
      ENNReal.ofReal_rpow_of_pos
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos h_va_pos D) (va * (va + vb)⁻¹)),
      ENNReal.ofReal_rpow_of_pos h_vb_pos,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h_vb_pos D),
      ENNReal.ofReal_rpow_of_pos
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos h_vb_pos D) (vb * (va + vb)⁻¹)),
      ← ENNReal.ofReal_mul h_expr_nonneg, ← ENNReal.ofReal_mul h_expr_2_nonneg,
      mul_inv] at h_result_simp
    have : ((va^D)^(va*(va + vb)⁻¹))^D⁻¹ = va^(va*(va + vb)⁻¹) := by
      rw [← Real.rpow_mul (Real.rpow_nonneg (le_of_lt h_va_pos) D),
        ← Real.rpow_mul (le_of_lt h_va_pos)]
      grind
    rw [this] at h_result_simp
    have : ((vb^D)^(vb*(va + vb)⁻¹))^D⁻¹ = vb^(vb*(va + vb)⁻¹) := by
      rw [← Real.rpow_mul (Real.rpow_nonneg (le_of_lt h_vb_pos) D),
        ← Real.rpow_mul (le_of_lt h_vb_pos)]
      congr 1; unfold D; field_simp
    rw [this] at h_result_simp
    have : ((va*(va+vb)⁻¹) ^ (va*(va+vb)⁻¹))⁻¹
        = (va^(va*(va+vb)⁻¹))⁻¹ * (va+vb)^(va*(va+vb)⁻¹) := by
      rw [← Real.inv_rpow ((le_mul_inv_iff₀ h_va_plus_vb_pos).mpr (by linarith)),
        mul_inv, inv_inv,
        Real.mul_rpow (inv_nonneg.mpr (le_of_lt h_va_pos)) (le_of_lt h_va_plus_vb_pos)]
      congr
      rw [Real.inv_rpow (le_of_lt h_va_pos)]
    rw [this] at h_result_simp
    have : ((vb*(va+vb)⁻¹) ^ (vb*(va+vb)⁻¹))⁻¹
        = (vb^(vb*(va+vb)⁻¹))⁻¹ * (va+vb)^(vb*(va+vb)⁻¹) := by
      rw [← Real.inv_rpow ((le_mul_inv_iff₀ h_va_plus_vb_pos).mpr (by linarith)),
        mul_inv, inv_inv,
        Real.mul_rpow (inv_nonneg.mpr (le_of_lt h_vb_pos)) (le_of_lt h_va_plus_vb_pos)]
      congr
      rw [Real.inv_rpow (le_of_lt h_vb_pos)]
    rw [this] at h_result_simp
    have : (va^(va*(va + vb)⁻¹))⁻¹ * (va + vb)^(va*(va + vb)⁻¹)
        * ((vb^(vb*(va + vb)⁻¹))⁻¹ * (va + vb)^(vb*(va + vb)⁻¹))
        * va^(va*(va + vb)⁻¹) * vb^(vb*(va + vb)⁻¹) = va + vb := calc
      _ = ((va^(va*(va + vb)⁻¹))⁻¹ * va^(va*(va + vb)⁻¹))
          * ((vb^(vb*(va + vb)⁻¹))⁻¹ * vb^(vb*(va + vb)⁻¹))
          * ((va + vb)^(va*(va + vb)⁻¹) * (va + vb)^(vb*(va + vb)⁻¹)) := by ring
      _ = ((va + vb)^(va*(va + vb)⁻¹) * (va + vb)^(vb*(va + vb)⁻¹)) := by
        field_simp
      _ = (va + vb)^(va*(va + vb)⁻¹ + vb*(va + vb)⁻¹) := by rw [Real.rpow_add h_va_plus_vb_pos]
      _ = va + vb := by field_simp; apply Real.rpow_one
    rw [this] at h_result_simp
    exact h_result_simp
  -- Final manipulation to remove ENNReal.ofReal and .toReal
  rw [ENNReal.ofReal_add (le_of_lt h_va_pos) (le_of_lt h_vb_pos),
    ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hvolAzero hvolAinf),
    ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hvolBzero hvolBinf),
    ENNReal.ofReal_toReal hvolAinf, ENNReal.ofReal_toReal hvolBinf] at h_result_simp_2
  exact h_result_simp_2

/-- Brunn–Minkowski for `EuclideanSpace ℝ (Fin (d + 1))` (a wrapper around `brunn_minkowski`).
@isnad1 id=le.5h3v.s11.e1449e505830 from=translated src=- shape=b1c5e603 vocab=25128f1b
-/
theorem _root_.Tengoku.MahlerHansenCograph.brunn_minkowski_euclideanSpace
    {d : ℕ} {A B : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : volume A ^ ((d:ℝ)+1)⁻¹ + volume B ^ ((d:ℝ)+1)⁻¹ ≤ volume (A + B) ^ ((d:ℝ)+1)⁻¹ := by
  let e : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm
  have h_add : e '' A + e '' B = e '' (A + B) := by
    ext
    simp only [mem_image, mem_add, exists_exists_and_eq_and]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a + b, add_mem_add ha hb, rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have h_vol : ∀ S, MeasurableSet S → volume (e '' S) = volume S := by
    intro S hS
    rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 1))).symm.map_eq,
      Measure.map_apply (by fun_prop) hS]
    congr
    aesop
  let h_bm : volume (e '' A) ^ ((d:ℝ)+1)⁻¹ + volume (e '' B) ^ ((d:ℝ)+1)⁻¹
      ≤ volume (e '' A + e '' B) ^ ((d:ℝ)+1)⁻¹ :=
    brunn_minkowski
      (hA_nonempty.image ⇑e) (e.measurableSet_image.mpr hA_measurable)
      (hB_nonempty.image ⇑e) (e.measurableSet_image.mpr hB_measurable)
      (by rw [h_add]; exact e.measurableSet_image.mpr hAB_measurable)
  rw [h_vol _ hA_measurable, h_vol _ hB_measurable, h_add, h_vol _ hAB_measurable] at h_bm
  exact h_bm

/-!
## Arbitrary finite coordinate types
-/

/-- Brunn--Minkowski for a nonempty finite coordinate type.
@isnad1 id=le.5h3v.s8.839b4caf27a2 from=translated src=- shape=69d31f36 vocab=7c0ce357
-/
theorem _root_.Tengoku.MahlerHansenCograph.brunn_minkowski_fintype
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {A B : Set (ι → ℝ)}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B)) :
    volume A ^ ((Fintype.card ι : ℝ)⁻¹) +
        volume B ^ ((Fintype.card ι : ℝ)⁻¹) ≤
      volume (A + B) ^ ((Fintype.card ι : ℝ)⁻¹) := by
  classical
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨d, hd⟩ : ∃ d, Fintype.card ι = d + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard)
  let indexEquiv : ι ≃ Fin (d + 1) := hd ▸ Fintype.equivFin ι
  let e : (ι → ℝ) ≃ᵐ (Fin (d + 1) → ℝ) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin (d + 1) => ℝ) indexEquiv
  have he : MeasurePreserving (⇑e) volume volume :=
    MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin (d + 1) => ℝ) indexEquiv
  have h_add : e '' A + e '' B = e '' (A + B) := by
    ext z
    simp only [mem_image, mem_add, exists_exists_and_eq_and]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a + b, add_mem_add ha hb, ?_⟩
      ext i
      simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      refine ⟨a, ha, b, hb, ?_⟩
      ext i
      simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have h_vol : ∀ S, MeasurableSet S → volume (e '' S) = volume S := by
    intro S hS
    rw [← he.map_eq,
      Measure.map_apply e.measurable (e.measurableSet_image.mpr hS)]
    congr
    exact e.injective.preimage_image S
  have hABimage : MeasurableSet (e '' A + e '' B) := by
    rw [h_add]
    exact e.measurableSet_image.mpr hAB_measurable
  have hbm :
      volume (e '' A) ^ ((d : ℝ) + 1)⁻¹ +
          volume (e '' B) ^ ((d : ℝ) + 1)⁻¹ ≤
        volume (e '' A + e '' B) ^ ((d : ℝ) + 1)⁻¹ :=
    brunn_minkowski (d := d) (A := e '' A) (B := e '' B)
    (hA_nonempty.image ⇑e) (e.measurableSet_image.mpr hA_measurable)
    (hB_nonempty.image ⇑e) (e.measurableSet_image.mpr hB_measurable)
    hABimage
  rw [h_vol A hA_measurable, h_vol B hB_measurable,
    h_add, h_vol (A + B) hAB_measurable] at hbm
  simpa [hd] using hbm

/-- Finite-volume real-valued form of `brunn_minkowski_fintype`.
@isnad1 id=le.8h3v.s9.b39503e76fd0 from=translated src=- shape=38518aeb vocab=34fa2046
-/
theorem _root_.Tengoku.MahlerHansenCograph.brunn_minkowski_fintype_toReal
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {A B : Set (ι → ℝ)}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    (hA_finite : volume A ≠ ⊤) (hB_finite : volume B ≠ ⊤)
    (hAB_finite : volume (A + B) ≠ ⊤) :
    Real.rpow (volume A).toReal ((Fintype.card ι : ℝ)⁻¹) +
        Real.rpow (volume B).toReal ((Fintype.card ι : ℝ)⁻¹) ≤
      Real.rpow (volume (A + B)).toReal ((Fintype.card ι : ℝ)⁻¹) := by
  let r : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hr : 0 ≤ r := by positivity
  have hAr : volume A ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr hA_finite
  have hBr : volume B ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr hB_finite
  have hABr : volume (A + B) ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hr hAB_finite
  have hbm := brunn_minkowski_fintype
    hA_nonempty hA_measurable hB_nonempty hB_measurable hAB_measurable
  have hreal :=
    (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hAr, hBr⟩) hABr).mpr hbm
  rw [ENNReal.toReal_add hAr hBr] at hreal
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at hreal
  simpa only [r, Real.rpow_eq_pow] using hreal
-- Tengoku: root names of this library moved to Tengoku.MahlerHansenCograph so they do not collide with other libraries (generated)
