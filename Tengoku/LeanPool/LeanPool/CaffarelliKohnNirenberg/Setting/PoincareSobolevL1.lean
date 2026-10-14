/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyL1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpOne
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Scaling
public import Tengoku
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormLeVecEuclidean

/-!
# The same-ball `W^{1,1}` to `L^{3/2}` estimate

The endpoint estimate is obtained by subtracting the ball average, applying the
two-reflection extension and a compact cutoff, and then using the global
Gagliardo--Nirenberg inequality at `p = 1`.  The affine bookkeeping is kept
explicit so that the final constant is independent of the ball.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Unit Euclidean ball used for the L¹ Poincare–Sobolev inequality. -/
def unitEuclideanBall : Set (Vec 3) :=
  euclideanBall (0 : Vec 3) 1

/--
@isnad1 id=isbounde.0h0v.s2.2df47c347a6c from=translated src=- shape=cef8a6bf vocab=70053689
-/
theorem unitEuclideanBall_bounded :
    IsBoundedDomain unitEuclideanBall := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx i
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  exact (abs_apply_le_vecEuclideanNorm x i).trans hx'.le

/-- Explicit L¹ Poincare coefficient on the unit Euclidean ball. -/
noncomputable def unitL1PoincareConstant : ℝ :=
  (volume unitEuclideanBall).toReal⁻¹ *
      (((2 * Classical.choose unitEuclideanBall_bounded) ^ 3) / (3 : ℝ)) *
    ((3 : ℝ) * (volume (Metric.ball (0 : Vec 3) 1)).toReal *
      (4 * Classical.choose unitEuclideanBall_bounded))

/-- The absolute unit-ball constant in the smooth `W^{1,1}` endpoint estimate. -/
noncomputable def poincareSobolevL1Constant : ℝ≥0∞ :=
  (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec 3)) (1 : ℝ) : ℝ≥0∞) *
    ((1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) +
      96 * (3 * 64 + 2 * 648 : ℝ≥0∞) * ENNReal.ofReal unitL1PoincareConstant)

end
end CKN
