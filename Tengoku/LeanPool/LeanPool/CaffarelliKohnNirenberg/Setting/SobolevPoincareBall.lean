/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyC1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyEnergy
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyGradient
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyPoincare
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyScaling
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth

/-!
# Unit-ball Sobolev localization through the two-reflection extension

The compactly supported cutoff of the `C¹` extension is the smooth input for the
same-ball estimate.  This module records the localization step explicitly; the
remaining reduction of its outer-ball terms to the original ball is kept separate.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

/--
@isnad1 id=contdiff.1h1v.s8.0783e2e659c9 from=translated src=- shape=1661dba1 vocab=f72e27c7
-/
theorem seeleyCutoffExtension_contDiff (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (seeleyCutoffExtension v) := by
  exact (canonicalBallCutoff_smooth (0 : Vec 3) (by norm_num) (by norm_num)
    |>.of_le (by simp)).mul (seeleyExtension_contDiff v hv)

/--
@isnad1 id=eq.1h2v.s6.14d178451d17 from=translated src=- shape=0f08941a vocab=63c9dc2a
-/
theorem seeleyCutoffExtension_eq_on_unitBall {v : Vec 3 → ℝ} {x : Vec 3}
    (hx : x ∈ euclideanBall (0 : Vec 3) 1) :
    seeleyCutoffExtension v x = v x := by
  have hnorm : vecEuclideanNorm (x - (0 : Vec 3)) < 1 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1 := by
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2 hnorm.le
  rw [seeleyCutoffExtension, Pi.mul_apply]
  rw [canonicalBallCutoff_eq_one_on_inner
    (x₀ := (0 : Vec 3)) (r := 1) (R := 2) (by norm_num) (by norm_num) hx]
  simp only [one_mul, seeleyExtension, hxC, ite_true]

/-- Finite coefficient in the L⁶ Poincare–Sobolev estimate on a Euclidean ball. -/
noncomputable def sobolevPoincareL6Constant : ℝ≥0∞ :=
  let Cg : ℝ≥0∞ :=
    2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) +
      2 * 32 ^ 2 * 6337 * euclideanBallPoincareConstant
  localSobolevConstant *
    (Cg ^ (1 / 2 : ℝ) +
      32 * ((6337 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        euclideanBallPoincareConstant ^ (1 / 2 : ℝ)))

end
end CKN
