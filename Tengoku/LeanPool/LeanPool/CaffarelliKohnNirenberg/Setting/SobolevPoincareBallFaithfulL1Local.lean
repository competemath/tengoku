/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantPos
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallMemLp
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Tengoku

/-!
# Approximation lemmas for Sobolev–Poincaré on Euclidean balls

These lemmas transfer smooth Euclidean-ball Poincaré estimates to W¹,¹ data.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-- The coordinatewise gradient sum is controlled by the Euclidean norm in dimension three.
@isnad1 id=le.0h1v.s5.07a68897185a from=translated src=- shape=21d16f2a vocab=c271d5ed
-/
theorem sum_abs_le_sqrt_three_vec3EuclideanNormFaithful (v : Vec3) :
    (∑ i : Fin 3, |v i|) ≤ Real.sqrt 3 * vec3EuclideanNorm v := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
    (fun _ : Fin 3 => (1 : ℝ)) (fun i : Fin 3 => |v i|)
  calc
    ∑ i : Fin 3, |v i| = ∑ i : Fin 3, (1 : ℝ) * |v i| := by simp
    _ ≤ Real.sqrt (∑ i : Fin 3, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ i : Fin 3, |v i| ^ 2) := hcs
    _ = Real.sqrt 3 * vec3EuclideanNorm v := by
      rw [show (∑ i : Fin 3, (1 : ℝ) ^ 2) = 3 by norm_num]
      congr 2
      exact Finset.sum_congr rfl (fun i _ => sq_abs _)

end
end CKN
