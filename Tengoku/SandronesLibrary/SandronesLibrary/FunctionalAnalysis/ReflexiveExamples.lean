/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.SeparableDual
import Tengoku.Seed.Analysis.InnerProductSpace.Dual
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 自反空间的标准实例

本文件沿用典范嵌入满射这一自反性表达，只证明有限维实赋范空间与完备实内积空间
两个标准正例。前者比较代数对偶与连续对偶的维数，后者直接使用 Riesz 表示。
-/

open Module
open RCLike
open scoped InnerProductSpace

namespace SandronesLibrary.FunctionalAnalysis

/-- 每个有限维实赋范空间都是自反的。

> **Entry**: functional-analysis.bidual.reflexive-examples-/
theorem finiteDimensional_reflexive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  let e₁ : Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  let _ : FiniteDimensional ℝ (StrongDual ℝ E) :=
    FiniteDimensional.of_surjective e₁.toLinearMap e₁.surjective
  let e₂ : Module.Dual ℝ (StrongDual ℝ E) ≃ₗ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
    LinearMap.toContinuousLinearMap
  let _ : FiniteDimensional ℝ (StrongDual ℝ (StrongDual ℝ E)) :=
    FiniteDimensional.of_surjective e₂.toLinearMap e₂.surjective
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (NormedSpace.inclusionInDoubleDualLi ℝ).injective
  calc
    finrank ℝ E = finrank ℝ (Module.Dual ℝ E) := Subspace.dual_finrank_eq.symm
    _ = finrank ℝ (StrongDual ℝ E) := e₁.finrank_eq
    _ = finrank ℝ (Module.Dual ℝ (StrongDual ℝ E)) := Subspace.dual_finrank_eq.symm
    _ = finrank ℝ (StrongDual ℝ (StrongDual ℝ E)) := e₂.finrank_eq

/-- 每个完备实内积空间都是自反的。-/
theorem realHilbert_reflexive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro Φ
  let R := InnerProductSpace.toDual ℝ E
  let g : StrongDual ℝ E := Φ.comp R.toContinuousLinearEquiv.toContinuousLinearMap
  let x : E := R.symm g
  refine ⟨x, ContinuousLinearMap.ext ?_⟩
  intro f
  change f x = Φ f
  calc
    f x = inner ℝ (R.symm f) x := InnerProductSpace.toDual_symm_apply.symm
    _ = inner ℝ x (R.symm f) := real_inner_comm _ _
    _ = g (R.symm f) := InnerProductSpace.toDual_symm_apply
    _ = Φ (R (R.symm f)) := rfl
    _ = Φ f := congrArg Φ (R.apply_symm_apply f)

end SandronesLibrary.FunctionalAnalysis
