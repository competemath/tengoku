/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.Monlib4.Preq.Ites

/-!
# LeanPool.Monlib4.Preq.Equiv

Imported Lean Pool material for `LeanPool.Monlib4.Preq.Equiv`.
-/

@[expose] public section

/--
@isnad1 id=mem.0h3v.s7.50e371b5e844 from=translated src=- shape=bf10af08 vocab=98048fda
-/
theorem Equiv.Perm.ToPequiv.toMatrix_mem_unitaryGroup {n : Type _} [DecidableEq n]
    [Fintype n] {𝕜 : Type _} [CommRing 𝕜] [StarRing 𝕜] (σ : Equiv.Perm n) :
    (Equiv.toPEquiv σ).toMatrix ∈ Matrix.unitaryGroup n 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.one_apply,
      Function.Injective.eq_iff (Equiv.injective σ), eq_comm, h]
