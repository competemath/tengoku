/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.KContinuity
import Tengoku.LeanPool.LeanPool.Feige.TransferProbability

/-!
# Nullity of the moving halfspace boundary

The continuity proof for `dirichletK` reduces to the fact that the
coordinate `E₀` has an atomless law and is independent of all other
coordinates.  This file supplies the atomlessness calculation for the
nonnegative exponential law and then applies the product decomposition of a
finite `Option`-indexed product.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Feige

/-- The pushed-forward nonnegative exponential law has no atoms.
@isnad1 id=eq.0h1v.s4.47d0a4710b0f from=translated src=- shape=778ca0af vocab=6b7d9ebc
-/
theorem nnexpMeasure_singleton (x : NNReal) :
    nnexpMeasure {x} = 0 := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  rw [nnexpMeasure, Measure.map_apply measurable_real_toNNReal
    (measurableSet_singleton x)]
  by_cases hx : x = 0
  · subst x
    have hpre :
        Real.toNNReal ⁻¹' ({0} : Set NNReal) = Set.Iic (0 : ℝ) := by
      ext r
      simp [Real.toNNReal_eq_zero]
    rw [hpre, ← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _)]
    rw [ExponentialTransfer.expMeasure_one_Ioi (x := 0) le_rfl]
    simp
  · have hpre :
        Real.toNNReal ⁻¹' ({x} : Set NNReal) = {(x : ℝ)} := by
      ext r
      simp only [mem_preimage, mem_singleton_iff]
      exact Real.toNNReal_eq_iff_eq_coe hx
    rw [hpre, ExponentialTransfer.expMeasure_one_singleton]

end Feige
