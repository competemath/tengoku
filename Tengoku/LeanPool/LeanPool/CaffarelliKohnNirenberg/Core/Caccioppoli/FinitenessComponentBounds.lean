/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationBall
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationCylinder
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability

/-! Componentwise norm estimates used by Caccioppoli finiteness arguments. -/

@[expose] public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology
noncomputable section

namespace CKN

theorem caccioppoli_native_norm_le_euclidean (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

end CKN
