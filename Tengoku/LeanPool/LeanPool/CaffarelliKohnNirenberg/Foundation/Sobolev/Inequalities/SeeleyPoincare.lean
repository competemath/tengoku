/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyGradient
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Lp
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import Tengoku

/-!
# Seeley Poincare

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

/-- Unit Euclidean ball used as the reference domain for the Seeley construction. -/
def seeleyUnitEuclideanBall : Set (Vec 3) :=
  euclideanBall (0 : Vec 3) 1

private theorem seeleyVecEuclideanNorm_eq_l2 (x : Vec 3) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ :=
  vecEuclideanNorm_eq_norm_toLp x

private theorem seeleyVecEuclideanNorm_add_le (x y : Vec 3) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [seeleyVecEuclideanNorm_eq_l2, seeleyVecEuclideanNorm_eq_l2,
    seeleyVecEuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem seeleyUnitEuclideanBall_open :
    IsOpen seeleyUnitEuclideanBall := by
  change IsOpen {x : Vec 3 | euclideanSqDist x 0 < (1 : ℝ) ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous
    continuous_const

private theorem seeleyUnitEuclideanBall_bounded :
    IsBoundedDomain seeleyUnitEuclideanBall := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx i
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  exact (abs_apply_le_vecEuclideanNorm x i).trans hx'.le

private theorem seeleyUnitEuclideanBall_convex :
    Convex ℝ seeleyUnitEuclideanBall := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rcases hz with ⟨a, b, ha, hb, hab, habz⟩
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hy' : vecEuclideanNorm y < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  simp only [sub_zero]
  rw [← habz]
  calc
    vecEuclideanNorm (a • x + b • y) ≤
        vecEuclideanNorm (a • x) + vecEuclideanNorm (b • y) :=
      seeleyVecEuclideanNorm_add_le _ _
    _ = a * vecEuclideanNorm x + b * vecEuclideanNorm y := by
      rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ < a * 1 + b * 1 := by
      by_cases hapos : 0 < a
      · exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx' hapos)
          (mul_le_mul_of_nonneg_left hy'.le hb)
      · have ha0 : a = 0 := le_antisymm (not_lt.mp hapos) ha
        have hbpos : 0 < b := by linarith only [hab, ha0]
        exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_left hx'.le ha)
          (mul_lt_mul_of_pos_left hy' hbpos)
    _ = 1 := by simp [hab]

/--
@isnad1 id=isopenbo.0h0v.s2.dcbbb08cba4f from=translated src=- shape=cef8a6bf vocab=3cc770c9
-/
theorem seeleyUnitEuclideanBall_domain :
    IsOpenBoundedConvexDomain seeleyUnitEuclideanBall :=
  ⟨seeleyUnitEuclideanBall_open, seeleyUnitEuclideanBall_bounded,
    seeleyUnitEuclideanBall_convex⟩

/-- Explicit L² Poincare coefficient on the unit Euclidean ball. -/
noncomputable def euclideanBallPoincareConstant : ℝ≥0∞ :=
  let A : ℝ :=
    (MeasureTheory.volume seeleyUnitEuclideanBall).toReal⁻¹ *
      (((2 * Classical.choose
        seeleyUnitEuclideanBall_domain.isBoundedDomain) ^ 3) / (3 : ℝ))
  let B : ℝ :=
    (3 : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec 3) 1)).toReal *
      (4 * Classical.choose seeleyUnitEuclideanBall_domain.isBoundedDomain)
  ENNReal.ofReal (9 * A ^ 2 * B ^ 2)

end
end CKN
