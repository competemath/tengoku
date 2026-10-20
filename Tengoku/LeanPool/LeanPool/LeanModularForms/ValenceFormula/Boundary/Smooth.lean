/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
public import Tengoku.LeanPool.LeanPool.LeanModularForms.ValenceFormula.Boundary.Basic
import Tengoku.LeanPool.LeanPool.LeanModularForms.GeneralizedResidueTheory.ArcCalculus
public import Tengoku.LeanPool.LeanPool.LeanModularForms.ValenceFormula.Boundary.Bounds
import Tengoku.Seed.CategoryTheory.Category.Init

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fundamental Domain Boundary – Smoothness

Differentiability, derivatives, limits, and curve/immersion constructions
for the fundamental domain boundary.

## Main Definitions

* `fdBoundaryHCurve` — H-parameterized boundary as `PiecewiseC1Curve`
* `fdBoundaryHImmersion` — H-parameterized boundary as `PiecewiseC1Immersion`
* `fdBoundaryCurve` — fixed-height boundary as `PiecewiseC1Curve`
* `fdBoundaryImmersion` — fixed-height boundary as `PiecewiseC1Immersion`
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
private instance : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
private instance : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul

-- The arc on t ∈ (1,3) is ArcCalculus.unitArc (π/3) (2π/3) 1 3.

private lemma hasDerivAt_seg5_fun (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (↑s - 9/2 : ℂ) + ↑H * I) (1 : ℂ) t := by
  refine ((((hasDerivAt_id t).ofReal_comp).sub (hasDerivAt_const t (9/2 : ℂ))).add
    (hasDerivAt_const t (↑H * I : ℂ))).congr_deriv ?_
  simp only [ofReal_one]; ring

lemma fdBoundary_H_hasDerivAt_seg5' (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (4 : ℝ) 5) :
    HasDerivAt (fdBoundaryH H) 1 t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s : ℝ => (↑s - 9/2 : ℂ) + ↑H * I := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s ⟨hs1, hs2⟩
    simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith,
      show ¬s ≤ 2 from by linarith, show ¬s ≤ 3 from by linarith,
      show ¬s ≤ 4 from by linarith, ite_false]
  exact (hasDerivAt_seg5_fun H t).congr_of_eventuallyEq heq

lemma fdBoundary_H_hasDerivAt_seg5 (H : ℝ) {t : ℝ} (h4 : 4 < t) :
    HasDerivAt (fdBoundaryH H) 1 t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s : ℝ => (↑s - 9/2 : ℂ) + ↑H * I := by
    filter_upwards [Ioi_mem_nhds h4] with s hs
    have hs4 : (4 : ℝ) < s := hs
    simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith,
      show ¬s ≤ 2 from by linarith, show ¬s ≤ 3 from by linarith,
      show ¬s ≤ 4 from by linarith, ite_false]
  exact (hasDerivAt_seg5_fun H t).congr_of_eventuallyEq heq

theorem continuous_fdBoundary_seg1_H (H : ℝ) :
    Continuous (fdBoundarySeg1H H) := by unfold fdBoundarySeg1H; fun_prop

theorem continuous_fdBoundary_seg4_H (H : ℝ) :
    Continuous (fdBoundarySeg4H H) := by unfold fdBoundarySeg4H; fun_prop

theorem continuous_fdBoundary_seg5_H (H : ℝ) :
    Continuous (fdBoundarySeg5H H) := by unfold fdBoundarySeg5H; fun_prop

lemma hasDerivAt_fdBoundary_seg1_H (H t : ℝ) :
    HasDerivAt (fdBoundarySeg1H H) (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundarySeg1H H = fun s : ℝ =>
      ((1 : ℂ) / 2 + ↑H * I) + ↑s * (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundarySeg1H]; push_cast; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by push_cast; ring)

lemma hasDerivAt_fdBoundary_seg4_H (H t : ℝ) :
    HasDerivAt (fdBoundarySeg4H H) ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundarySeg4H H = fun s : ℝ =>
      ((-1 : ℂ) / 2 + ↑(Real.sqrt 3) / 2 * I) +
        ↑(s - 3) * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundarySeg4H]; push_cast; ring
  rw [hfun]
  have h_sub : HasDerivAt (fun s : ℝ => (↑(s - 3) : ℂ)) 1 t := by
    have := ((hasDerivAt_id t).sub (hasDerivAt_const t (3 : ℝ))).ofReal_comp
    simp only [sub_zero, ofReal_one] at this; exact this
  exact (h_sub.mul_const _).const_add _ |>.congr_deriv (by push_cast; ring)

lemma hasDerivAt_fdBoundary_seg5_H (H t : ℝ) :
    HasDerivAt (fdBoundarySeg5H H) 1 t := by
  have hfun : fdBoundarySeg5H H = fun s : ℝ =>
      ((-9 / 2 : ℂ) + ↑H * I) + ↑s * (1 : ℂ) := by ext s; simp only [fdBoundarySeg5H]; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by norm_cast)

/-- Boilerplate: an `=ᶠ[𝓝[≤] p]` equality from agreement on `Ioo a b ∩ Iic p`. -/
private lemma eventuallyEq_nhdsLE_of_Ioo {f g : ℝ → ℂ} (a b : ℝ) {p : ℝ} (ha : a < p) (hb : p < b)
    (h : ∀ s ∈ Ioo a b ∩ Iic p, f s = g s) : f =ᶠ[𝓝[≤] p] g :=
  Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo a b ∩ Iic p, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds ha hb)) self_mem_nhdsWithin, h⟩

/-- Boilerplate: an `=ᶠ[𝓝[≥] p]` equality from agreement on `Ioo a b ∩ Ici p`. -/
private lemma eventuallyEq_nhdsGE_of_Ioo {f g : ℝ → ℂ} (a b : ℝ) {p : ℝ} (ha : a < p) (hb : p < b)
    (h : ∀ s ∈ Ioo a b ∩ Ici p, f s = g s) : f =ᶠ[𝓝[≥] p] g :=
  Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo a b ∩ Ici p, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds ha hb)) self_mem_nhdsWithin, h⟩

private lemma seg4_eventuallyEq_left_4 (H : ℝ) :
    fdBoundarySeg4H H =ᶠ[𝓝[≤] 4] fdBoundaryH H :=
  eventuallyEq_nhdsLE_of_Ioo 3 5 (by norm_num) (by norm_num) fun s hs => by
    rcases eq_or_lt_of_le (show s ≤ 4 from hs.2) with rfl | h
    · simp only [fdBoundarySeg4H, fdBoundary_H_at_four]; push_cast; ring
    · exact (fdBoundary_H_eq_seg4_H (by linarith [hs.1.1]) (le_of_lt h)).symm

private lemma seg5_eventuallyEq_right_4 (H : ℝ) :
    fdBoundarySeg5H H =ᶠ[𝓝[≥] 4] fdBoundaryH H :=
  eventuallyEq_nhdsGE_of_Ioo 3 5 (by norm_num) (by norm_num) fun s hs => by
    rcases eq_or_lt_of_le (show (4 : ℝ) ≤ s from hs.2) with rfl | h
    · simp only [fdBoundarySeg5H, fdBoundary_H_at_four]; push_cast; ring
    · exact (fdBoundary_H_eq_seg5_H h).symm

lemma fdBoundary_H_not_differentiableAt_4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundaryH H) 4 := by
  intro hdiff
  have hleft : HasDerivWithinAt (fdBoundaryH H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Iic 4) 4 :=
    ((seg4_eventuallyEq_left_4 H).hasDerivWithinAt_iff (by
      simp only [fdBoundarySeg4H, fdBoundary_H_at_four]; push_cast; ring)).mp
      (hasDerivAt_fdBoundary_seg4_H H 4).hasDerivWithinAt
  have hright : HasDerivWithinAt (fdBoundaryH H) 1 (Ici 4) 4 :=
    ((seg5_eventuallyEq_right_4 H).hasDerivWithinAt_iff (by
      simp only [fdBoundarySeg5H, fdBoundary_H_at_four]; push_cast; ring)).mp
      (hasDerivAt_fdBoundary_seg5_H H 4).hasDerivWithinAt
  have hd := hdiff.hasDerivAt
  have him := congr_arg Complex.im
    (((uniqueDiffWithinAt_Iic (4 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt).trans
      ((uniqueDiffWithinAt_Ici (4 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt).symm)
  simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, one_im] at him
  linarith [sub_pos.mpr hH]

lemma fdBoundary_H_deriv_continuousOn_Ioo_45 (H : ℝ) :
    ContinuousOn (deriv (fdBoundaryH H)) (Ioo 4 5) := by
  intro t ht
  have : deriv (fdBoundaryH H) =ᶠ[𝓝 t]
      fun _ => (1 : ℂ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv
  exact this.continuousAt.continuousWithinAt

end
