/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import Tengoku

/-!
# Translated mollifiers as spatial test functions

The slice form of a distributional identity is obtained by testing the
space-time identity against the countable family of mollifier bumps centred at
the points of a countable dense set.  This file records the elementary
properties of a single translated bump `x ↦ mollifier ε (x - y)`: it is smooth,
compactly supported with topological support the closed ball `closedBall y ε`,
and its coordinate derivative is the translate of the coordinate derivative of
the kernel.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace CKN

/-- The mollifier vanishes outside its closed ball of radius `ε`.
@isnad1 id=eq.2h3v.s5.3f46aee499a5 from=translated src=- shape=0d8c792b vocab=72e6ca34
-/
theorem mollifier_eq_zero_of_lt_norm {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : ε < ‖z‖) : mollifier (d := d) ε hε z = 0 := by
  have hts : tsupport (mollifier (d := d) ε hε) = closedBall (0 : Vec d) ε :=
    (standardMollifier (d := d) ε hε).tsupport_normed_eq
  have hz' : z ∉ tsupport (mollifier (d := d) ε hε) := by
    rw [hts, mem_closedBall, dist_zero_right]
    exact not_le.2 hz
  exact image_eq_zero_of_notMem_tsupport hz'

/-- Each coordinate derivative of the mollifier vanishes outside the closed ball
of radius `ε`.
@isnad1 id=eq.2h4v.s8.6e6030649df0 from=translated src=- shape=bdbb266d vocab=a5e20d78
-/
theorem fderiv_mollifier_apply_eq_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : ε < ‖z‖) (i : Fin d) :
    (fderiv ℝ (mollifier (d := d) ε hε) z) (basisVec i) = 0 := by
  have hts : tsupport (mollifier (d := d) ε hε) = closedBall (0 : Vec d) ε :=
    (standardMollifier (d := d) ε hε).tsupport_normed_eq
  have hz' : z ∉ tsupport (mollifier (d := d) ε hε) := by
    rw [hts, mem_closedBall, dist_zero_right]
    exact not_le.2 hz
  rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hz']
  simp

/-- Each coordinate derivative of the mollifier is continuous.
@isnad1 id=continuo.1h3v.s8.3dbed145b356 from=translated src=- shape=3038356b vocab=3ec3268d
-/
theorem continuous_fderiv_mollifier_apply {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin d) :
    Continuous fun z : Vec d => (fderiv ℝ (mollifier (d := d) ε hε) z) (basisVec i) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (mollifier (d := d) ε hε) :=
    mollifier_contDiff (d := d) hε
  simpa using (hk.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The translated mollifier is smooth.
@isnad1 id=contdiff.1h3v.s7.7193a1ecf8c6 from=translated src=- shape=33b40885 vocab=d9310e62
-/
theorem contDiff_mollifier_sub {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => mollifier (d := d) ε hε (x - y) :=
  (mollifier_contDiff (d := d) hε).comp (contDiff_id.sub contDiff_const)

/-- The translated mollifier has compact support.
@isnad1 id=hascompa.1h3v.s6.1138a780040b from=translated src=- shape=1f0cc618 vocab=e53783c8
-/
theorem hasCompactSupport_mollifier_sub {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    HasCompactSupport fun x : Vec d => mollifier (d := d) ε hε (x - y) := by
  simpa [Function.comp_def] using
    (mollifier_hasCompactSupport (d := d) hε).comp_homeomorph (Homeomorph.subRight y)

/-- The topological support of the translated mollifier is the closed ball of
radius `ε` about the translation point.
@isnad1 id=eq.1h3v.s6.bc149150f306 from=translated src=- shape=0eace281 vocab=e753689d
-/
theorem tsupport_mollifier_sub_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    tsupport (fun x : Vec d => mollifier (d := d) ε hε (x - y)) = closedBall y ε := by
  have hts : tsupport (fun x : Vec d => mollifier (d := d) ε hε (x - y))
      = (Homeomorph.subRight y) ⁻¹' tsupport (mollifier (d := d) ε hε) := by
    simpa [Function.comp_def] using
      tsupport_comp_eq_preimage (mollifier (d := d) ε hε) (Homeomorph.subRight y)
  have hk : tsupport (mollifier (d := d) ε hε) = closedBall (0 : Vec d) ε :=
    (standardMollifier (d := d) ε hε).tsupport_normed_eq
  rw [hts, hk]
  ext x
  simp [Homeomorph.subRight, mem_closedBall, dist_eq_norm]

/-- The coordinate derivative of a translated mollifier is the translate of the
coordinate derivative of the mollifier.
@isnad1 id=eq.1h5v.s9.cbd413172b38 from=translated src=- shape=35ecd52d vocab=32fd0e47
-/
theorem fderiv_mollifier_sub_apply {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y x : Vec d)
    (i : Fin d) :
    (fderiv ℝ (fun z : Vec d => mollifier (d := d) ε hε (z - y)) x) (basisVec i)
      = (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i) := by
  have hinner : HasFDerivAt (fun z : Vec d => z - y)
      (ContinuousLinearMap.id ℝ (Vec d)) x := (hasFDerivAt_id x).sub_const y
  have houter : HasFDerivAt (mollifier (d := d) ε hε)
      (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (x - y) :=
    ((mollifier_contDiff (d := d) (n := 1) hε).differentiable (by simp) (x - y)).hasFDerivAt
  have hcomp := houter.comp x hinner
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv

end CKN

end
