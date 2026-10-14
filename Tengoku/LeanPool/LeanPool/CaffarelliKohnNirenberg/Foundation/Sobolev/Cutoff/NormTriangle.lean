/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import Tengoku

/-!
# Norm Triangle

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

/-- The Euclidean norm on native coordinate vectors coincides with the `L²`
norm of `WithLp.toLp 2 x`.
@isnad1 id=eq.0h2v.s6.80229d42b8c2 from=translated src=- shape=755c25e9 vocab=56ed39da
-/
theorem vecEuclideanNorm_eq_norm_toLp {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The triangle inequality for the Euclidean norm on native coordinate vectors.
@isnad1 id=le.0h3v.s5.45aa79685d51 from=translated src=- shape=e4bc9e79 vocab=c475e8d1
-/
theorem vecEuclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [vecEuclideanNorm_eq_norm_toLp, vecEuclideanNorm_eq_norm_toLp, vecEuclideanNorm_eq_norm_toLp]
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

end CKN
