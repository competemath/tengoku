/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile
public import Tengoku

/-!
# Time Cutoff

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace CKN

/-- A smooth backward cutoff with its transition confined to a time interval. -/
def backwardTimeCutoff (t h s : ℝ) : ℝ :=
  1 - smoothTransitionProfile ((s - (t - h / 2)) / (h / 2))

/--
@isnad1 id=contdiff.0h2v.s5.4643fe282a1b from=translated src=- shape=7c676072 vocab=0c0d2f80
-/
theorem backwardTimeCutoff_smooth {t h : ℝ} :
    ContDiff ℝ (⊤ : ℕ∞) (backwardTimeCutoff t h) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (s - (t - h / 2)) / (h / 2)) := by
    exact ((contDiff_id.sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : ℝ => t - h / 2))).div_const (h / 2))
  unfold backwardTimeCutoff
  apply contDiff_const.sub
  exact smoothTransitionProfile.smooth.comp harg

/--
@isnad1 id=le.0h3v.s4.5d8b26281411 from=translated src=- shape=ac9c39a3 vocab=049ca0f4
-/
theorem backwardTimeCutoff_nonneg {t h s : ℝ} :
    0 ≤ backwardTimeCutoff t h s := by
  unfold backwardTimeCutoff
  linarith only [smoothTransitionProfile.le_one
    ((s - (t - h / 2)) / (h / 2))]

/--
@isnad1 id=le.0h3v.s4.2776f028011d from=translated src=- shape=87ce733d vocab=049ca0f4
-/
theorem backwardTimeCutoff_le_one {t h s : ℝ} :
    backwardTimeCutoff t h s ≤ 1 := by
  unfold backwardTimeCutoff
  linarith only [smoothTransitionProfile.nonneg
    ((s - (t - h / 2)) / (h / 2))]

/--
@isnad1 id=eq.2h3v.s5.b7cafbe6158e from=translated src=- shape=233a6c75 vocab=eb378654
-/
theorem backwardTimeCutoff_eq_one_of_le {t h s : ℝ} (hh : 0 < h)
    (hs : s ≤ t - h) : backwardTimeCutoff t h s = 1 := by
  unfold backwardTimeCutoff
  rw [smoothTransitionProfile.zero_of_nonpos]
  · norm_num
  · apply (div_nonpos_iff).2
    right
    exact ⟨by linarith only [hs, hh], by positivity⟩

/--
@isnad1 id=eq.2h3v.s5.be4f444b41de from=translated src=- shape=0abf8801 vocab=88d108d0
-/
theorem backwardTimeCutoff_eq_zero_of_ge {t h s : ℝ} (hh : 0 < h)
    (hs : t ≤ s) : backwardTimeCutoff t h s = 0 := by
  unfold backwardTimeCutoff
  rw [smoothTransitionProfile.one_of_one_le]
  · norm_num
  · apply (le_div_iff₀ (by positivity)).2
    linarith only [hs, hh]

/--
@isnad1 id=eq.1h2v.s6.a737ce8c7fc4 from=translated src=- shape=3b51fcc7 vocab=202c29e7
-/
theorem backwardTimeCutoff_integral_deriv {t h : ℝ} (hh : 0 < h) :
    ∫ s in t - h..t, deriv (backwardTimeCutoff t h) s = -1 := by
  have hfund := intervalIntegral.integral_deriv_eq_sub
    (f := backwardTimeCutoff t h) (a := t - h) (b := t)
    (fun s hs => (backwardTimeCutoff_smooth (t := t) (h := h)).differentiable
      (by simp) s)
    (by
      have hcont : Continuous (deriv (backwardTimeCutoff t h)) :=
        (backwardTimeCutoff_smooth (t := t) (h := h)).continuous_deriv (by simp)
      exact hcont.intervalIntegrable _ _)
  rw [backwardTimeCutoff_eq_zero_of_ge hh le_rfl,
    backwardTimeCutoff_eq_one_of_le hh le_rfl] at hfund
  simpa using hfund

private lemma backwardTimeCutoff_deriv_eq_zero_of_lt {t h s : ℝ}
    (hh : 0 < h) (hs : s < t - h) :
    deriv (backwardTimeCutoff t h) s = 0 := by
  have hev : backwardTimeCutoff t h =ᶠ[𝓝 s] (fun _ : ℝ => 1) := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    exact backwardTimeCutoff_eq_one_of_le hh (le_of_lt hy)
  exact (hasDerivAt_const s 1).congr_of_eventuallyEq hev |>.deriv

private lemma backwardTimeCutoff_deriv_eq_zero_of_gt {t h s : ℝ}
    (hh : 0 < h) (hs : t < s) :
    deriv (backwardTimeCutoff t h) s = 0 := by
  have hev : backwardTimeCutoff t h =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
    filter_upwards [Ici_mem_nhds hs] with y hy
    exact backwardTimeCutoff_eq_zero_of_ge hh hy
  exact (hasDerivAt_const s 0).congr_of_eventuallyEq hev |>.deriv

/--
@isnad1 id=le.1h2v.s6.5db5aeb09e45 from=translated src=- shape=919b5699 vocab=94177fe0
-/
theorem backwardTimeCutoff_kernel_support {t h : ℝ} (hh : 0 < h) :
    Function.support (fun s => -deriv (backwardTimeCutoff t h) s) ⊆ Icc (t - h) t := by
  intro s hs
  by_contra hnot
  have houtside : s < t - h ∨ t < s := by
    simpa only [mem_Icc, not_and_or, not_le] using hnot
  rcases houtside with hleft | hright
  · exact (Function.mem_support.mpr hs)
      (by rw [neg_eq_zero, backwardTimeCutoff_deriv_eq_zero_of_lt hh hleft])
  · exact (Function.mem_support.mpr hs)
      (by rw [neg_eq_zero,
        backwardTimeCutoff_deriv_eq_zero_of_gt (t := t) (h := h) (s := s) hh hright])

/--
@isnad1 id=eq.1h2v.s6.875b1c513a52 from=translated src=- shape=2d487653 vocab=1ef5bb37
-/
theorem backwardTimeCutoff_kernel_integral {t h : ℝ} (hh : 0 < h) :
    ∫ s, -deriv (backwardTimeCutoff t h) s = 1 := by
  have hsupp := backwardTimeCutoff_kernel_support (t := t) (h := h) hh
  have hind : (Icc (t - h) t).indicator
      (fun s => -deriv (backwardTimeCutoff t h) s) =
      (fun s => -deriv (backwardTimeCutoff t h) s) :=
    indicator_eq_self.2 hsupp
  rw [← hind, integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (a := t - h) (b := t)
    (by linarith only [hh])]
  rw [intervalIntegral.integral_neg,
    backwardTimeCutoff_integral_deriv (t := t) (h := h) hh]
  norm_num

end CKN
