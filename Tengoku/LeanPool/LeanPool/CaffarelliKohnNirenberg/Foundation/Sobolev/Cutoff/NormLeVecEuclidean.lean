/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic

/-!
# Norm Le Vec Euclidean

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

/-- The sup norm of a vector of `Vec d` is at most its Euclidean norm.
@isnad1 id=le.0h2v.s5.2a6bd31a81c5 from=translated src=- shape=e4284abf vocab=11aff1bd
-/
theorem pi_norm_le_vecEuclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i _
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

end CKN
