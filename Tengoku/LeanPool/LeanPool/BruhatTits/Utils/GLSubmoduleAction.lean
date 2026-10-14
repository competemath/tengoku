/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Tengoku.LeanPool.LeanPool.BruhatTits.Utils.Matrix

/-!
# LeanPool.BruhatTits.Utils.GLSubmoduleAction
-/

@[expose] public section

open Module

variable {K : Type*} [Field K]
variable {R : Subring K}

namespace BruhatTits
open Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
@isnad1 id=eq.0h6v.s14.486132f16c24 from=translated src=- shape=a2f33205 vocab=50288167
-/
lemma scalar_smul_GL_smul (M : Submodule R (ι → K))
    (a : K) (g : GL ι K) : a • g • M = g • a • M := by
  ext x
  simp only [Matrix.GeneralLinearGroup.mem_smul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨a • z, ?_, ?_⟩
    · use z, hz
      rfl
    · simp [Matrix.mulVec_smul]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simp only [DistribSMul.toLinearMap_apply, Matrix.mulVec_smul]
    refine ⟨g.val.mulVec z, ?_, rfl⟩
    simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul]
    use z, hz

/--
@isnad1 id=le.1h6v.s12.bce10349b1b2 from=translated src=- shape=bb8e8761 vocab=f8b625d9
-/
lemma smul_GL_mono {M L : Submodule R (ι → K)} (g : GL ι K) (hML : M ≤ L) : g • M ≤ g • L := by
  intro x
  simp only [Matrix.GeneralLinearGroup.mem_smul, forall_exists_index, and_imp]
  rintro y hy rfl
  use y, (hML hy)

/--
@isnad1 id=iff.0h6v.s12.7d868084c23b from=translated src=- shape=cf1ff4b7 vocab=f8b625d9
-/
lemma smul_le_iff {M L : Submodule R (ι → K)} (g : GL ι K) : g • M ≤ g • L ↔ M ≤ L := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_GL_mono _ h⟩
  rw [← one_smul (GL ι K) M, ← one_smul (GL ι K) L, ← inv_mul_cancel g, mul_smul, mul_smul]
  exact smul_GL_mono _ h

/--
@isnad1 id=iff.0h6v.s11.53999cbe90b6 from=translated src=- shape=a63bb3d4 vocab=530ff9ea
-/
lemma smul_eq_iff (g : GL ι K) (M L : Submodule R (ι → K)) :
    g • M = g • L ↔ M = L := by
  simp_all

/--
@isnad1 id=iff.0h6v.s12.da08bbccf1cc from=translated src=- shape=a63bb3d4 vocab=67129116
-/
lemma smul_lt_iff (g : GL ι K) (M L : Submodule R (ι → K)) : g • M < g • L ↔ M < L := by
  constructor
  · intro h
    by_contra hnotlt
    simp [eq_of_le_of_not_lt ((smul_le_iff g).mp (le_of_lt h)) hnotlt] at h
  · intro h
    by_contra hnotlt
    have := eq_of_le_of_not_lt ((smul_le_iff g).mpr (le_of_lt h)) hnotlt
    simp_all

end BruhatTits
