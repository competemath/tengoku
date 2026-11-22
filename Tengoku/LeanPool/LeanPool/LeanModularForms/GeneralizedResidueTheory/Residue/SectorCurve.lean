/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.CategoryTheory.Category.Init
import Tengoku.Seed.Combinatorics.Matroid.Init
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool
namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sector Curve PV Computation (Lemma 3.1)

Model sector-curve and PV integral computations for Laurent series terms.
This implements the key computation from Hungerbuhler-Wasem (arXiv:1808.00997v2)
Lemma 3.1: the principal value of `dz/z` along a sector curve equals `i * alpha`,
where `alpha` is the opening angle of the sector.

## Main Definitions

* `sectorCurve` -- the model sector-curve parameterized on [0,3]

## Main Results

* `pv_sector_dz_over_z` -- PV of `dz/z` along sector curve equals `I * alpha`

See `SectorCurveLemma.lean` for higher-order results (`pv_sector_higher_power`,
`cauchyPV_sectorCurve_simplePole`, etc.).

## Mathematical Overview

The sector curve `sigma_{r,alpha}` is a closed curve from the origin, along the
positive real axis to radius `r`, then around an arc of angle `alpha`, then back
to the origin along the ray at angle `alpha`. Specifically:

* Segment 1 (`t in [0,1]`): radial ray `t |-> t * r` (outgoing along real axis)
* Segment 2 (`t in [1,2]`): arc `t |-> r * exp(i * (t-1) * alpha)` at radius `r`
* Segment 3 (`t in [2,3]`): radial ray `t |-> (3-t) * r * exp(i * alpha)` (returning)

The PV of `dz/z` along this curve decomposes as:
* Segments 1 and 3 contribute symmetric logarithmic divergences that cancel
* Segment 2 contributes `int_0^alpha i d theta = i * alpha`

Reference: Hungerbuhler-Wasem, arXiv:1808.00997v2, Lemma 3.1.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Definition of the sector curve -/

/-- The model sector curve parameterized on [0,3].
- [0,1]: radial ray from 0 to r along the positive real axis
- [1,2]: circular arc of radius r from angle 0 to angle alpha
- [2,3]: radial ray from r*exp(i*alpha) back to 0 -/
def sectorCurve (r : ℝ) (α : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then
    ↑(t * r)
  else if t ≤ 2 then
    ↑r * exp (I * ↑((t - 1) * α))
  else
    ↑((3 - t) * r) * exp (I * ↑α)

/-! ### Basic properties of the sector curve -/

/-- The sector curve at t=0 is 0.
@isnad1 id=eq.0h2v.s4.442512d56cac from=translated src=- shape=b5500b83 vocab=479ce82e
-/
theorem sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by simp [sectorCurve]

/-- The sector curve at t=3 is 0.
@isnad1 id=eq.0h2v.s4.a334f7554728 from=translated src=- shape=b5500b83 vocab=821034c9
-/
theorem sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by
  simp only [sectorCurve, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, ↓reduceIte, sub_self, zero_mul,
    Complex.ofReal_zero, zero_mul]

/-- The sector curve is a closed curve (starts and ends at 0).
@isnad1 id=eq.0h2v.s4.ac9012fbaa6e from=translated src=- shape=336f71ee vocab=821034c9
-/
theorem sectorCurve_closed (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = sectorCurve r α 3 := by rw [sectorCurve_zero, sectorCurve_three]

/-- The sector curve at t=1 is r (the transition from radial to arc).
@isnad1 id=eq.0h2v.s4.8e1b8389cca1 from=translated src=- shape=e185e377 vocab=8b854051
-/
theorem sectorCurve_one (r : ℝ) (α : ℝ) :
    sectorCurve r α 1 = ↑r := by simp [sectorCurve]

/-- The sector curve at t=2 is r * exp(i * alpha) (end of arc).
@isnad1 id=eq.0h2v.s5.71d6bac513c2 from=translated src=- shape=f0f7d537 vocab=28424e80
-/
theorem sectorCurve_two (r : ℝ) (α : ℝ) :
    sectorCurve r α 2 = ↑r * exp (I * ↑α) := by
  simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num, show (2 : ℝ) ≤ 2 from le_refl 2,
    ↓reduceIte]; congr 1; congr 1; push_cast; ring

/-- Segment 1: for t in [0,1], the sector curve is `t * r`.
@isnad1 id=eq.1h3v.s5.5dcddfe77889 from=translated src=- shape=237634f7 vocab=153dc331
-/
theorem sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    sectorCurve r α t = ↑(t * r) := by simp [sectorCurve, ht.2]

/-- Segment 2: for t in [1,2], the sector curve is `r * exp(i*(t-1)*alpha)`.
@isnad1 id=eq.1h3v.s6.af5a4fd55781 from=translated src=- shape=a871fcd1 vocab=0f5c1e5e
-/
theorem sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) :
    sectorCurve r α t = ↑r * exp (I * ↑((t - 1) * α)) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h1
  · simp [sectorCurve, Complex.exp_zero]
  · simp only [sectorCurve, ite_eq_right (not_le.mpr h1), ite_eq_left ht.2]

/-- Segment 3: for t in [2,3], the sector curve is `(3-t)*r * exp(i*alpha)`.
@isnad1 id=eq.1h3v.s6.d39fdca05e16 from=translated src=- shape=f55845a4 vocab=0f5c1e5e
-/
theorem sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    sectorCurve r α t = ↑((3 - t) * r) * exp (I * ↑α) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h2
  · simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num,
      show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
    push_cast; ring_nf
  · simp only [sectorCurve, ite_eq_right (not_le.mpr (lt_trans one_lt_two h2)),
      ite_eq_right (not_le.mpr h2)]

/-- The sector curve is continuous on [0,3].
@isnad1 id=continuo.0h2v.s5.abc5b080c7f0 from=translated src=- shape=eaa034ba vocab=cca1c6bd
-/
theorem sectorCurve_continuousOn (r : ℝ) (α : ℝ) :
    ContinuousOn (sectorCurve r α) (Icc 0 3) := by
  have h_union : Icc (0 : ℝ) 3 = Icc 0 1 ∪ Icc 1 2 ∪ Icc 2 3 := by
    ext x; simp only [mem_Icc, mem_union]
    constructor
    · intro ⟨h0, h3⟩
      by_cases h1 : x ≤ 1
      · exact Or.inl (Or.inl ⟨h0, h1⟩)
      · push Not at h1; by_cases h2 : x ≤ 2
        · exact Or.inl (Or.inr ⟨le_of_lt h1, h2⟩)
        · push Not at h2; exact Or.inr ⟨le_of_lt h2, h3⟩
    · rintro ((⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩) <;> exact ⟨by linarith, by linarith⟩
  rw [h_union]
  have hc1 : ContinuousOn (sectorCurve r α) (Icc 0 1) :=
    (continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn.congr
      (fun t ht => sectorCurve_seg1 r α t ht)
  have hc2 : ContinuousOn (sectorCurve r α) (Icc 1 2) :=
    (continuousOn_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (continuous_ofReal.comp ((continuous_id.sub continuous_const).mul
        continuous_const)))).continuousOn).congr (fun t ht => sectorCurve_seg2 r α t ht)
  have hc3 : ContinuousOn (sectorCurve r α) (Icc 2 3) :=
    ((continuous_ofReal.comp ((continuous_const.sub continuous_id).mul
      continuous_const)).continuousOn.mul continuousOn_const).congr
      (fun t ht => sectorCurve_seg3 r α t ht)
  exact ((hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc)

/-- The sector curve passes through the origin at t=0 and t=3.
@isnad1 id=and.0h2v.s5.3d7b58216562 from=translated src=- shape=696023ef vocab=821034c9
-/
theorem sectorCurve_passes_through_origin (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 ∧ sectorCurve r α 3 = 0 :=
  ⟨sectorCurve_zero r α, sectorCurve_three r α⟩

/-- On the arc segment (t in [1,2]), the sector curve has modulus r.
@isnad1 id=eq.2h3v.s5.42574e96c9c6 from=translated src=- shape=cb81f1a1 vocab=3c6abee6
-/
theorem sectorCurve_norm_on_arc (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ)
    (ht : t ∈ Icc 1 2) :
    ‖sectorCurve r α t‖ = r := by
  rw [sectorCurve_seg2 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg (le_of_lt hr)

/-! ### Derivative of the sector curve -/

/-- Derivative on segment 1 (t in (0,1)): `deriv (sectorCurve r alpha) t = r`.
@isnad1 id=eq.1h3v.s6.5bc93ce27faf from=translated src=- shape=c4632f28 vocab=b82c3293
-/
theorem deriv_sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    deriv (sectorCurve r α) t = ↑r := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑(s * r) := by
    have h_nhds : Iio 1 ∈ 𝓝 t := Iio_mem_nhds ht.2
    filter_upwards [h_nhds] with s hs
    simp only [sectorCurve, ite_eq_left (le_of_lt (mem_Iio.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h1 : HasDerivAt (fun s => s * r) r t := by simpa using (hasDerivAt_id t).mul_const r
  exact h1.ofReal_comp.deriv

/-- Derivative on segment 2 (t in (1,2)):
  `deriv (sectorCurve r alpha) t = r * (I * alpha) * exp(I * (t-1) * alpha)`.
@isnad1 id=eq.1h3v.s7.0e6c210aaf99 from=translated src=- shape=dd8aac0c vocab=d8c08ae0
-/
theorem deriv_sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    deriv (sectorCurve r α) t =
      ↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑r * exp (I * ↑((s - 1) * α)) := by
    have h_nhds : Ioo 1 2 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    filter_upwards [h_nhds] with s hs
    rw [sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((s - 1) * α) : ℂ)) (↑α) t := by
    have h1 : HasDerivAt (fun s => (s - 1) * α) α t := by
      simpa using ((hasDerivAt_id t).sub_const 1).mul_const α
    exact h1.ofReal_comp
  have h_exp : HasDerivAt (fun s => exp (I * ↑((s - 1) * α)))
      (I * ↑α * exp (I * ↑((t - 1) * α))) t := by
    have := (hasDerivAt_exp (I * ↑((t - 1) * α))).comp t
      ((hasDerivAt_const t I).mul h_inner)
    exact this.congr_deriv (by ring)
  have h_full : HasDerivAt (fun s => ↑r * exp (I * ↑((s - 1) * α)))
      (↑r * (I * ↑α * exp (I * ↑((t - 1) * α)))) t := by
    have := (hasDerivAt_const t (↑r : ℂ)).mul h_exp
    exact this.congr_deriv (by ring)
  rw [h_full.deriv]; ring

/-- Derivative on segment 3 (t in (2,3)):
  `deriv (sectorCurve r alpha) t = -r * exp(I * alpha)`.
@isnad1 id=eq.1h3v.s6.df42409f9583 from=translated src=- shape=4cc2ab59 vocab=9b330e28
-/
theorem deriv_sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    deriv (sectorCurve r α) t = -(↑r) * exp (I * ↑α) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑((3 - s) * r) * exp (I * ↑α) := by
    have h_nhds : Ioi 2 ∈ 𝓝 t := Ioi_mem_nhds ht.1
    filter_upwards [h_nhds] with s hs
    simp only [sectorCurve,
      ite_eq_right (not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) (mem_Ioi.mp hs))),
      ite_eq_right (not_le.mpr (mem_Ioi.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((3 - s) * r) : ℂ)) (↑(-r)) t := by
    have h1 : HasDerivAt (fun s => (3 - s) * r) (-r) t := by
      have := ((hasDerivAt_const t 3).sub (hasDerivAt_id t)).mul_const r
      exact this.congr_deriv (by ring)
    exact h1.ofReal_comp
  have h_full : HasDerivAt (fun s => ↑((3 - s) * r) * exp (I * ↑α))
      (↑(-r) * exp (I * ↑α)) t :=
    h_inner.mul_const _
  rw [h_full.deriv]; push_cast; ring

/-! ### PV integrand analysis -/

/-- The integrand `(sectorCurve r alpha t)^(-1) * deriv (sectorCurve r alpha) t`
on segment 1 (t in (0,1)) simplifies to `1/t` (as a complex number).
@isnad1 id=eq.2h3v.s6.0d29cefcf198 from=translated src=- shape=98794eed vocab=055fe4b6
-/
theorem pv_integrand_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = ↑(t⁻¹) := by
  rw [sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ht]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  push_cast; field_simp

/-- The integrand on segment 2 (t in (1,2)) simplifies to `I * alpha`.
@isnad1 id=eq.2h3v.s6.6922df631da0 from=translated src=- shape=4f5c76e9 vocab=cf82acf9
-/
theorem pv_integrand_seg2 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α := by
  rw [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h_exp_ne : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The integrand on segment 3 (t in (2,3)) simplifies to `-1/(3-t)`.
@isnad1 id=eq.2h3v.s7.e75710068b3d from=translated src=- shape=4e2eb6c7 vocab=ea14ff4f
-/
theorem pv_integrand_seg3 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = -↑((3 - t)⁻¹) := by
  rw [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg3 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h_exp_ne : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
  have h3t_ne : (3 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h3t_ne' : (↑(3 - t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h3t_ne
  push_cast; field_simp

/-! ### PV computation: Lemma 3.1 -/

/-- The integral of `1/t` from `epsilon` to `1` is `-log(epsilon)`.
@isnad1 id=eq.2h1v.s5.0968df9a7906 from=translated src=- shape=650d8d76 vocab=5a41fe49
-/
theorem integral_seg1_eq_neg_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by
  simp_all

/-- The integral of `-1/(3-t)` from `2` to `3-epsilon` is `log(epsilon)`.
@isnad1 id=eq.2h1v.s6.189cd85641e8 from=translated src=- shape=bff88638 vocab=762b5df7
-/
theorem integral_seg3_eq_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (2 : ℝ)..(3 - ε), -((3 - t)⁻¹) = Real.log ε := by
  rw [intervalIntegral.integral_neg]
  have h1 : ∫ t in (2 : ℝ)..(3 - ε), (3 - t)⁻¹ = ∫ u in ε..1, u⁻¹ := by
    have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
      (a := (2 : ℝ)) (b := 3 - ε)
    rw [this]
    congr 1 <;> ring
  simp_all

/-- On segment 1, the norm of the sector curve is `t * r`.
@isnad1 id=eq.2h3v.s5.71fa83732794 from=translated src=- shape=449750a1 vocab=8f9c55db
-/
theorem sectorCurve_norm_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖sectorCurve r α t‖ = t * r := by
  rw [sectorCurve_seg1 r α t ht]
  exact Complex.norm_of_nonneg (mul_nonneg ht.1 (le_of_lt hr))

/-- On segment 3, the norm of the sector curve is `(3 - t) * r`.
@isnad1 id=eq.2h3v.s6.d349d67799cc from=translated src=- shape=46087afd vocab=3ceb0665
-/
theorem sectorCurve_norm_seg3' (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    ‖sectorCurve r α t‖ = (3 - t) * r := by
  rw [sectorCurve_seg3 r α t ht, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_of_nonneg (mul_nonneg (by linarith [ht.2]) (le_of_lt hr))]

/-- The logarithmic integrals from segments 1 and 3 cancel.
@isnad1 id=eq.3h2v.s7.f17e65471e61 from=translated src=- shape=3588d022 vocab=10d74fee
-/
theorem log_cancellation (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ)) +
    (∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ)) = 0 := by
  have hεr_pos : 0 < ε / r := div_pos hε hr
  have hεr_lt1 : ε / r < 1 := by rwa [div_lt_one hr]
  have h1 : ∫ t in (ε / r)..(1 : ℝ), (t⁻¹ : ℝ) = -(Real.log (ε / r)) := by
    rw [integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero (ne_of_gt hεr_pos),
      Real.log_one, zero_sub]
  have h2 : ∫ t in (2 : ℝ)..(3 - ε / r), -((3 - t)⁻¹ : ℝ) = Real.log (ε / r) := by
    rw [intervalIntegral.integral_neg]
    have h_sub : ∫ t in (2 : ℝ)..(3 - ε / r), (3 - t)⁻¹ = ∫ u in (ε / r)..1, u⁻¹ := by
      have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
        (a := (2 : ℝ)) (b := 3 - ε / r)
      rw [this]; congr 1 <;> ring
    simp_all
  have h1c : ∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ) = ↑(-(Real.log (ε / r))) := by
    rw [← h1, intervalIntegral.integral_ofReal]
  have h2c : ∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ) =
      ↑(Real.log (ε / r)) := by
    have : ∀ t : ℝ, (-(↑((3 - t)⁻¹) : ℂ)) = (↑((-((3 - t)⁻¹)) : ℝ)) := by
      intro t; push_cast; ring
    simp_rw [this, intervalIntegral.integral_ofReal, h2]
  rw [h1c, h2c, ← Complex.ofReal_add, neg_add_cancel, Complex.ofReal_zero]

end
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
