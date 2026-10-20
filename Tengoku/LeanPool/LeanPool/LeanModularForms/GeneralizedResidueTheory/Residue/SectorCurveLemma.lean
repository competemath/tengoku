/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.SectorCurve
public import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue
import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import Tengoku.Seed.Analysis.Calculus.Deriv.ZPow
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Arctan
import Tengoku.Seed.CategoryTheory.Category.Init
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.MeasureTheory.Covering.Besicovitch
import Tengoku.Seed.MeasureTheory.Integral.DivergenceTheorem
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sector Curve PV Lemmas

Higher-order PV computations and the generalized winding number for the
model sector-curve defined in `SectorCurve.lean`.

## Main Results

* `pv_sector_higher_power` -- for n >= 1, `PV int z^{n-1} dz = 0` (angle condition)
* `cauchyPV_sectorCurve_simplePole` -- Lemma 3.1 for simple poles: PV = `I * alpha * residue`
* `cauchyPV_sectorCurve_eq_mul_residueSimplePole` -- variant for arbitrary `f = c/z + g`
* `pv_sector_negative_power` -- Equation (3.4): PV of `z^{-n}` is 0 under angle condition
* `generalizedWindingNumber_sectorCurve` -- winding number equals `alpha / (2 * pi)`
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private theorem sectorCurve_differentiableAt_off_knots (r : ℝ) (α : ℝ)
    (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 3) (ht_not : t ∉ ({1, 2} : Set ℝ)) :
    DifferentiableAt ℝ (sectorCurve r α) t := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_not
  rcases lt_or_gt_of_ne ht_not.1 with h1 | h1
  · have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => (↑(s * r) : ℂ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      simp only [sectorCurve, ite_eq_left (le_of_lt (mem_Iio.mp hs))]
    exact h_eq.differentiableAt_iff.mpr
      ((hasDerivAt_id t).mul_const r).ofReal_comp.differentiableAt
  · rcases lt_or_gt_of_ne ht_not.2 with h2 | h2
    · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
          fun s => (↑r : ℂ) * exp (I * ↑((s - 1) * α)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with s hs
        exact sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      refine h_eq.differentiableAt_iff.mpr ?_
      apply DifferentiableAt.const_mul; apply DifferentiableAt.cexp
      apply DifferentiableAt.const_mul
      exact (((hasDerivAt_id t).sub
        (hasDerivAt_const t (1 : ℝ))).mul_const α).ofReal_comp.differentiableAt
    · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
          fun s => (↑((3 - s) * r) : ℂ) * exp (I * ↑α) := by
        filter_upwards [Ioi_mem_nhds h2] with s hs
        simp only [sectorCurve,
          ite_eq_right (not_le.mpr (lt_trans one_lt_two (mem_Ioi.mp hs))),
          ite_eq_right (not_le.mpr (mem_Ioi.mp hs))]
      refine h_eq.differentiableAt_iff.mpr ?_
      apply DifferentiableAt.mul_const
      exact (((hasDerivAt_const t (3 : ℝ)).sub
        (hasDerivAt_id t)).mul_const r).ofReal_comp.differentiableAt

private theorem pow_integrableOn_01 (r : ℝ) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t) volume 0 1 :=
  ((show ContinuousOn (fun t => (↑(t * r) : ℂ) ^ (n - 1) * (↑r : ℂ))
    (Set.uIcc 0 1) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ht])

private theorem pow_integrableOn_12 (r : ℝ) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t) volume 1 2 :=
  ((show ContinuousOn (fun t => ((↑r : ℂ) * exp (I * ↑((t - 1) * α))) ^ (n - 1) *
      (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α))))
    (Set.uIcc 1 2) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem pow_integrableOn_23 (r : ℝ) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t) volume 2 3 :=
  ((show ContinuousOn (fun t => ((↑((3 - t) * r) : ℂ) * exp (I * ↑α)) ^ (n - 1) *
      (-(↑r : ℂ) * exp (I * ↑α)))
    (Set.uIcc 2 3) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg3 r α t ht])

/-- For `n >= 1`, the integral of `z^(n-1) dz` along the sector curve is 0
when `n * alpha` is a multiple of `2 * pi`. -/
theorem pv_sector_higher_power (r : ℝ) (_hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi)
    (n : ℕ) (hn : 1 ≤ n) (_h_angle : ∃ k : ℤ, n * α = k * (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..3,
      (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t = 0 := by
  set f : ℝ → ℂ := fun t =>
    (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t
  set F : ℝ → ℂ := fun t => (sectorCurve r α t) ^ n / (↑n : ℂ)
  have hF_cont : ContinuousOn F (Icc 0 3) :=
    ((sectorCurve_continuousOn r α).pow n).div_const _
  have hS_count : ({1, 2} ∩ Ioo (0 : ℝ) 3 : Set ℝ).Countable :=
    (Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable
  have hγ_diff : ∀ t ∈ Ioo (0 : ℝ) 3,
      t ∉ ({1, 2} : Set ℝ) → DifferentiableAt ℝ (sectorCurve r α) t :=
    sectorCurve_differentiableAt_off_knots r α
  have hF_deriv : ∀ t ∈ Ioo (0 : ℝ) 3 \ ({1, 2} ∩ Ioo (0 : ℝ) 3),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
    change HasDerivAt F (sectorCurve r α t ^ (n - 1) * deriv (sectorCurve r α) t) t
    refine (((hγ_diff t ht ht_not').hasDerivAt.pow n).div_const (↑n : ℂ)).congr_deriv ?_
    rw [mul_assoc, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (by omega) : (↑n : ℂ) ≠ 0)]
  have hf_int : IntervalIntegrable f volume 0 3 :=
    (pow_integrableOn_01 r α n).trans (pow_integrableOn_12 r α n) |>.trans
      (pow_integrableOn_23 r α n)
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f (by norm_num : (0 : ℝ) ≤ 3) hS_count hF_cont hF_deriv hf_int]
  change F 3 - F 0 = 0
  simp only [F, sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0),
    zero_div, sub_self]

private theorem sectorCurve_ne_zero_of_Icc_δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) :
    ∀ t ∈ Icc δ (3 - δ), sectorCurve r α t ≠ 0 := by
  intro t ht h0
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨le_trans hδ_pos.le ht.1, h1⟩] at h0
    have : t * r = 0 := Complex.ofReal_eq_zero.mp h0
    rcases mul_eq_zero.mp this with ht0 | hr0
    · linarith [ht.1]
    · linarith
  · rcases le_or_gt t 2 with h2 | h2
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩] at h0
      simp_all
    · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, by linarith [ht.2]⟩] at h0
      rcases mul_eq_zero.mp h0 with h3t | hexp0
      · have : (3 - t) * r = 0 := Complex.ofReal_eq_zero.mp h3t
        rcases mul_eq_zero.mp this with ht3 | hr0
        · linarith [ht.2]
        · linarith
      · exact absurd hexp0 (Complex.exp_ne_zero _)

private theorem sectorCurve_norm_le_near_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (_hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ * r = ε) :
    ∀ t ∈ Icc 0 δ, ‖sectorCurve r α t‖ ≤ ε := by
  intro t ht
  rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1, le_trans ht.2 hδ_lt_1.le⟩]
  calc t * r ≤ δ * r := mul_le_mul_of_nonneg_right ht.2 hr.le
    _ = ε := hδr_eq

private theorem sectorCurve_norm_le_near_three (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ * r = ε) :
    ∀ t ∈ Icc (3 - δ) 3, ‖sectorCurve r α t‖ ≤ ε := by
  intro t ht
  rw [sectorCurve_norm_seg3' r hr α t ⟨le_trans (by linarith : 2 ≤ 3 - δ) ht.1, ht.2⟩]
  calc (3 - t) * r ≤ δ * r := by apply mul_le_mul_of_nonneg_right _ hr.le; linarith [ht.1]
    _ = ε := hδr_eq

private theorem sectorCurve_norm_gt_mid (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) (ε : ℝ) (hε_lt_r : ε < r)
    (hδr_eq : δ * r = ε) :
    ∀ t ∈ Ioo δ (3 - δ), ε < ‖sectorCurve r α t‖ := by
  intro t ht
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ_pos ht.1), h1⟩]
    calc ε = δ * r := hδr_eq.symm
      _ < t * r := mul_lt_mul_of_pos_right ht.1 hr
  · rcases le_or_gt t 2 with h2 | h2
    · have : ‖sectorCurve r α t‖ = r :=
        sectorCurve_norm_on_arc r hr α t ⟨le_of_lt h1, h2⟩
      rw [this]; exact hε_lt_r
    · rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt h2, by linarith [ht.2]⟩]
      calc ε = δ * r := hδr_eq.symm
        _ < (3 - t) * r := by apply mul_lt_mul_of_pos_right _ hr; linarith [ht.2]

private theorem zpow_integrableOn_δ1 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume δ 1 := by
  have : ContinuousOn (fun t => (↑(t * r) : ℂ) ^ (-(↑n : ℤ)) * (↑r : ℂ))
      (Icc δ 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.zpow₀
      · fun_prop
      · intro t ht
        left; exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (lt_of_lt_of_le hδ_pos ht.1) hr))
    · exact continuousOn_const
  exact (this.intervalIntegrable_of_Icc hδ_lt_1.le).congr_ae (by
    rw [Set.uIoc_of_le hδ_lt_1.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨le_of_lt (lt_trans hδ_pos ht.1), le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ_pos ht.1, ht.2⟩])

private theorem zpow_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume 1 2 := by
  have : ContinuousOn (fun t => (↑r * exp (I * ↑((t - 1) * α))) ^ (-(↑n : ℤ)) *
      (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)))) (Icc 1 2) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.zpow₀
      · fun_prop
      · intro t _; left
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) (Complex.exp_ne_zero _)
    · fun_prop
  exact (this.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem zpow_integrableOn_23δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume 2 (3 - δ) := by
  have h3δ_gt_2 : 2 < 3 - δ := by linarith
  have : ContinuousOn (fun t => (↑((3 - t) * r) * exp (I * ↑α)) ^ (-(↑n : ℤ)) *
      (-(↑r) * exp (I * ↑α))) (Icc 2 (3 - δ)) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.zpow₀
      · fun_prop
      · intro t ht; left
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by linarith [ht.2]) hr)))
          (Complex.exp_ne_zero _)
    · exact continuousOn_const
  exact (this.intervalIntegrable_of_Icc h3δ_gt_2.le).congr_ae (by
    rw [Set.uIoc_of_le h3δ_gt_2.le,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, by linarith [ht.2]⟩,
      deriv_sectorCurve_seg3 r α t ⟨ht.1, by linarith [ht.2]⟩])

private theorem zpow_primitive_hasDerivAt (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    let m : ℤ := 1 - ↑n
    let γ := sectorCurve r α
    let F := fun t => (γ t) ^ m / (m : ℂ)
    let f := fun t => (γ t) ^ (-(↑n : ℤ)) * deriv γ t
    ∀ t ∈ Ioo δ (3 - δ) \ ({1, 2} ∩ Ioo δ (3 - δ)),
      HasDerivAt F (f t) t := by
  intro m γ F f t ⟨ht, ht_not⟩
  have hm_ne : (m : ℂ) ≠ 0 := by
    have : m ≠ 0 := by simp [m]; omega
    exact_mod_cast this
  have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
  have hγ_ne := sectorCurve_ne_zero_of_Icc_δ r hr α δ hδ_pos
    hδ_lt_1 t (Ioo_subset_Icc_self ht)
  have h_zpow : HasDerivAt (fun s => (γ s) ^ m)
      (((m : ℂ) * (γ t) ^ (m - 1)) • deriv γ t) t :=
    (hasDerivAt_zpow m (γ t) (Or.inl hγ_ne)).comp t
      (sectorCurve_differentiableAt_off_knots r α t
        ⟨lt_trans hδ_pos ht.1, lt_of_lt_of_le ht.2 (by linarith)⟩ ht_not').hasDerivAt
  have hm_sub : m - 1 = -(↑n : ℤ) := by simp [m]
  change HasDerivAt F ((γ t) ^ (-(↑n : ℤ)) * deriv γ t) t
  refine (h_zpow.div_const (m : ℂ)).congr_deriv ?_
  rw [smul_eq_mul, mul_assoc, mul_div_cancel_left₀ _ hm_ne, hm_sub]

private theorem zpow_ftc_vanishes (r : ℝ) (_hr : 0 < r) (α : ℝ) (n : ℕ) (_hn : 2 ≤ n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1)
    (h_exp_one : exp (I * ↑((1 - (↑(n : ℤ) : ℤ)) * α)) = 1) :
    let m : ℤ := 1 - ↑n
    let γ := sectorCurve r α
    let F := fun t => (γ t) ^ m / (m : ℂ)
    F (3 - δ) - F δ = 0 := by
  intro m γ F
  have h3δ_gt_2 : 2 < 3 - δ := by linarith
  have hγ_δ : γ δ = ↑(δ * r) := sectorCurve_seg1 r α δ ⟨hδ_pos.le, hδ_lt_1.le⟩
  have hγ_3δ : γ (3 - δ) = ↑(δ * r) * exp (I * ↑α) := by
    have := sectorCurve_seg3 r α (3 - δ) ⟨h3δ_gt_2.le, by linarith⟩
    simp only [show 3 - (3 - δ) = δ from by ring] at this; exact this
  simp only [F, hγ_δ, hγ_3δ, mul_zpow]
  rw [show (exp (I * ↑α)) ^ m = exp (I * ↑((1 - (↑n : ℤ)) * α)) from by
    rw [← Complex.exp_int_mul]; congr 1; push_cast [m]; ring, h_exp_one, mul_one, sub_self]

private theorem angle_condition_exp_eq_one (n : ℕ) (hn : 2 ≤ n) (α : ℝ)
    (k : ℤ) (hk : (↑(n - 1) : ℤ) * α = k * (2 * Real.pi)) :
    exp (I * ↑((1 - (↑n : ℤ)) * α)) = 1 := by
  suffices h : ∃ j : ℤ, I * ↑((1 - (↑n : ℤ)) * α) = ↑j * (2 * ↑Real.pi * I) by
    obtain ⟨j, hj⟩ := h; rw [hj]; exact Complex.exp_int_mul_two_pi_mul_I j
  exact ⟨-k, by
    have h1 : ((1 - (↑n : ℤ)) * α : ℝ) = ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hk ⊢; linarith
    rw [show (↑((1 - (↑n : ℤ)) * α) : ℂ) = ↑(((-k : ℤ) : ℝ) * (2 * Real.pi)) from
      congrArg _ h1]
    push_cast; ring⟩

private theorem pv_cutoff_integral_eq_mid (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    let δ := ε / r
    let γ := sectorCurve r α
    let f := fun t => (γ t) ^ (-(↑n : ℤ)) * deriv γ t
    ∫ t in (0 : ℝ)..3,
      (if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0) =
    ∫ t in δ..(3 - δ), f t := by
  intro δ γ f
  set g : ℝ → ℂ := fun t =>
    if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0
  have hδ_pos : 0 < δ := div_pos hε_pos hr
  have hδ_lt_1 : δ < 1 := by rw [div_lt_one hr]; exact hε_lt_r
  have hδr_eq : δ * r = ε := div_mul_cancel₀ ε (ne_of_gt hr)
  have h_norm_le_0δ := sectorCurve_norm_le_near_zero r hr α δ hδ_pos hδ_lt_1 ε hδr_eq
  have h_norm_le_3δ3 := sectorCurve_norm_le_near_three r hr α δ hδ_lt_1 ε hδr_eq
  have h_norm_gt_mid := sectorCurve_norm_gt_mid r hr α δ hδ_pos hδ_lt_1 ε hε_lt_r hδr_eq
  have hf_int : IntervalIntegrable f volume δ (3 - δ) :=
    (zpow_integrableOn_δ1 r hr α n δ hδ_pos hδ_lt_1).trans
      (zpow_integrableOn_12 r hr α n) |>.trans
      (zpow_integrableOn_23δ r hr α n δ hδ_pos hδ_lt_1)
  have hg_zero_left : ∀ t ∈ Set.uIcc (0 : ℝ) δ, g t = 0 := fun t ht => by
    simp only [g, sub_zero]
    rw [Set.uIcc_of_le hδ_pos.le] at ht
    rw [ite_eq_right (not_lt.mpr (h_norm_le_0δ t ht))]
  have hg_zero_right : ∀ t ∈ Set.uIcc (3 - δ) 3, g t = 0 := fun t ht => by
    simp only [g, sub_zero]
    rw [Set.uIcc_of_le (by linarith : 3 - δ ≤ 3)] at ht
    rw [ite_eq_right (not_lt.mpr (h_norm_le_3δ3 t ht))]
  have hg_eq_f_mid : ∀ᵐ x ∂volume, x ∈ Ioc δ (3 - δ) → g x = f x := by
    rw [ae_iff]
    apply measure_mono_null (t := {3 - δ})
    · intro x hx
      simp only [mem_ofPred_eq] at hx; push Not at hx
      obtain ⟨hx_ioc, hx_ne⟩ := hx
      by_contra hne_3δ
      simp only [mem_singleton_iff] at hne_3δ
      have hx_ioo : x ∈ Ioo δ (3 - δ) := ⟨hx_ioc.1, lt_of_le_of_ne hx_ioc.2 hne_3δ⟩
      exact hx_ne (by simp only [g, sub_zero, f]; rw [ite_eq_left (h_norm_gt_mid x hx_ioo)])
    · exact Real.volume_singleton
  have h_01 : ∫ t in (0 : ℝ)..δ, g t = 0 :=
    intervalIntegral.integral_zero_ae (ae_of_all _ (fun t ht =>
      hg_zero_left t (Set.uIoc_subset_uIcc ht)))
  have h_3δ3 : ∫ t in (3 - δ)..3, g t = 0 :=
    intervalIntegral.integral_zero_ae (ae_of_all _ (fun t ht =>
      hg_zero_right t (Set.uIoc_subset_uIcc ht)))
  have h_mid : ∫ t in δ..(3 - δ), g t = ∫ t in δ..(3 - δ), f t :=
    intervalIntegral.integral_congr_ae (by
      rw [Set.uIoc_of_le (by linarith : δ ≤ 3 - δ)]; exact hg_eq_f_mid)
  have hg_eq_f_mid' : g =ᵐ[volume.restrict (Set.uIoc δ (3 - δ))] f := by
    rw [Set.uIoc_of_le (by linarith : δ ≤ 3 - δ), Filter.EventuallyEq,
      ae_restrict_iff' measurableSet_Ioc]; exact hg_eq_f_mid
  have hg_0δ : IntervalIntegrable g volume 0 δ :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr_ae
      ((ae_restrict_mem measurableSet_uIoc).mono fun t ht =>
        (hg_zero_left t (Set.uIoc_subset_uIcc ht)).symm)
  have hg_δ3δ : IntervalIntegrable g volume δ (3 - δ) :=
    hf_int.congr_ae hg_eq_f_mid'.symm
  have hg_3δ3 : IntervalIntegrable g volume (3 - δ) 3 :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr_ae
      ((ae_restrict_mem measurableSet_uIoc).mono fun t ht =>
        (hg_zero_right t (Set.uIoc_subset_uIcc ht)).symm)
  rw [show ∫ t in (0 : ℝ)..3,
        (if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0) =
      ∫ t in (0 : ℝ)..3, g t from rfl]
  rw [← intervalIntegral.integral_add_adjacent_intervals hg_0δ (hg_δ3δ.trans hg_3δ3),
      ← intervalIntegral.integral_add_adjacent_intervals hg_δ3δ hg_3δ3,
      h_01, h_mid, h_3δ3, zero_add, add_zero]

/-- **Equation (3.4)**: The PV of `z^{-n}` along the sector curve is 0 when
`(n-1) * α` is a multiple of `2π`. The cutoff integral equals
`ε^{1-n} * (exp(i(1-n)α) - 1) / (1-n)`, which vanishes identically under
the angle condition. By FTC with primitive `F(t) = γ(t)^{1-n}/(1-n)`. -/
theorem pv_sector_negative_power (r : ℝ) (hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi)
    (n : ℕ) (hn : 2 ≤ n)
    (h_angle : ∃ k : ℤ, (↑(n - 1) : ℤ) * α = k * (2 * Real.pi)) :
    CauchyPrincipalValueExists' (fun z => z ^ (-(↑n : ℤ))) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => z ^ (-(↑n : ℤ))) (sectorCurve r α) 0 3 0 = 0 := by
  obtain ⟨k, hk⟩ := h_angle
  set γ := sectorCurve r α
  set m : ℤ := 1 - ↑n
  have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in (0 : ℝ)..3,
        (if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0) =
      0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr] with ε hε hε_pos
    simp only [mem_Ioi] at hε_pos
    set δ := ε / r
    have hδ_pos : 0 < δ := div_pos hε_pos hr
    have hδ_lt_1 : δ < 1 := by rw [div_lt_one hr]; exact mem_Iio.mp hε
    have hγ_ne := sectorCurve_ne_zero_of_Icc_δ r hr α δ hδ_pos hδ_lt_1
    have hF_cont : ContinuousOn (fun t => (γ t) ^ m / (m : ℂ)) (Icc δ (3 - δ)) := by
      apply ContinuousOn.div_const; apply ContinuousOn.zpow₀
      · exact (sectorCurve_continuousOn r α).mono (by
          intro t ht; constructor <;> linarith [ht.1, ht.2, hδ_pos])
      · intro t ht; exact Or.inl (hγ_ne t ht)
    have hf_int : IntervalIntegrable
        (fun t => (γ t) ^ (-(↑n : ℤ)) * deriv γ t) volume δ (3 - δ) :=
      (zpow_integrableOn_δ1 r hr α n δ hδ_pos hδ_lt_1).trans
        (zpow_integrableOn_12 r hr α n) |>.trans
        (zpow_integrableOn_23δ r hr α n δ hδ_pos hδ_lt_1)
    rw [pv_cutoff_integral_eq_mid r hr α n ε hε_pos (mem_Iio.mp hε),
      MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        _ _ (by linarith : δ ≤ 3 - δ)
        ((Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable) hF_cont
        (zpow_primitive_hasDerivAt r hr α n hn δ hδ_pos hδ_lt_1) hf_int]
    exact zpow_ftc_vanishes r hr α n hn δ hδ_pos hδ_lt_1
      (angle_condition_exp_eq_one n hn α k hk)
  have h_tendsto : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..3,
        if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' (h_ev.mono fun ε h => h.symm)
  exact ⟨⟨0, h_tendsto⟩, h_tendsto.limUnder_eq⟩

end
