/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.LocalBox
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import Tengoku

/-!
# Smooth localization inside a parabolic ball

A ball compactly inside the space-time domain admits a smooth cutoff and
a compactly interior product box containing its support.
-/

@[expose] public section

open Set Metric
open scoped Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Endgame

/-- A positive interior parabolic ball supplies a compactly interior spatial
ball and time interval. -/
theorem localBox_of_parabolic_ball
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) (hball : ball z₀ (2 * r) ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball z₀.1 r) (Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2)) := by
  have htime : z₀.2 - r ^ 2 < z₀.2 + r ^ 2 := by
    have hr2 := sq_pos_of_pos hr
    linarith only [hr2]
  refine ⟨isOpen_vec3Ball _ _, ?_, ?_, ordConnected_Ioo, ?_, ?_⟩
  · rw [closure_vec3Ball hr]
    have hcompact := vec3Homeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (vec3Homeomorph z₀.1) r)
    convert hcompact using 1
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall,
      vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2]
  · rw [closure_vec3Ball hr]
    intro x hx
    have hmem : dist (parabolicHomeomorph.symm (x, z₀.2)) z₀ < 2 * r := by
      rw [dist_eq_parabolicDist]
      change max (vec3EuclideanNorm (x - z₀.1)) (Real.sqrt |z₀.2 - z₀.2|) < 2 * r
      rw [sub_self, abs_zero, Real.sqrt_zero]
      exact max_lt (lt_of_le_of_lt hx (by linarith only [hr])) (by positivity)
    exact (hball hmem).1
  · rw [closure_Ioo htime.ne]
    exact isCompact_Icc
  · rw [closure_Ioo htime.ne]
    intro t ht
    have hmem : dist (parabolicHomeomorph.symm (z₀.1, t)) z₀ < 2 * r := by
      rw [dist_eq_parabolicDist]
      change max (vec3EuclideanNorm (z₀.1 - z₀.1)) (Real.sqrt |t - z₀.2|) < 2 * r
      rw [sub_self, vec3EuclideanNorm_zero]
      apply max_lt (by positivity)
      have habs : |t - z₀.2| ≤ r ^ 2 := abs_le.mpr
        ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
      exact (Real.sqrt_le_iff.mpr ⟨hr.le, habs⟩).trans_lt (by linarith only [hr])
    exact (hball hmem).2

end CKN.Core.Endgame
