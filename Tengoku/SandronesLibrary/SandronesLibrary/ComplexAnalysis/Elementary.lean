/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 初等复函数的全纯性

本文件在本库的教材全纯接口下处理复指数、复正弦、复余弦，并以通过非零点 `a`
的射线补集为定义域构造局部对数分支。Mathlib 的微分定理仅作为证明后端；全纯性结论
均通过 `HolomorphicOnTextbook` 给出。
-/

namespace SandronesLibrary.ComplexAnalysis

/-- 局部对数分支的定义域：`z / a` 避开非正实轴。
> **Entry**: complex-analysis.holomorphic.elementary-/
def localLogDomain (a : ℂ) : Set ℂ :=
  {z | z / a ∈ Complex.slitPlane}

/-- 以 `a` 为基点的局部对数分支。
> **Entry**: complex-analysis.holomorphic.elementary-/
noncomputable def localLogAt (a z : ℂ) : ℂ :=
  Complex.log (z / a) + Complex.log a

/-- 复指数函数在整个复平面上全纯。
> **Entry**: complex-analysis.holomorphic.elementary-/
theorem exp_holomorphic : HolomorphicOnTextbook Complex.exp Set.univ := by
  rw [holomorphicOnTextbook_iff_forall_differentiableAt]
  intro z _
  exact Complex.differentiable_exp.differentiableAt

/-- 复指数函数的导数等于它自身。-/
theorem exp_hasDerivAt (z : ℂ) : HasDerivAt Complex.exp (Complex.exp z) z := by
  exact Complex.hasDerivAt_exp z

/-- 复正弦函数在整个复平面上全纯。
> **Entry**: complex-analysis.holomorphic.elementary-/
theorem sin_holomorphic : HolomorphicOnTextbook Complex.sin Set.univ := by
  rw [holomorphicOnTextbook_iff_forall_differentiableAt]
  intro z _
  exact Complex.differentiable_sin.differentiableAt

/-- 复正弦函数的导数是复余弦。-/
theorem sin_hasDerivAt (z : ℂ) : HasDerivAt Complex.sin (Complex.cos z) z := by
  exact Complex.hasDerivAt_sin z

/-- 复余弦函数在整个复平面上全纯。
> **Entry**: complex-analysis.holomorphic.elementary-/
theorem cos_holomorphic : HolomorphicOnTextbook Complex.cos Set.univ := by
  rw [holomorphicOnTextbook_iff_forall_differentiableAt]
  intro z _
  exact Complex.differentiable_cos.differentiableAt

/-- 复余弦函数的导数是负的复正弦。-/
theorem cos_hasDerivAt (z : ℂ) : HasDerivAt Complex.cos (-Complex.sin z) z := by
  exact Complex.hasDerivAt_cos z

/-- 局部对数的定义域是开集。-/
theorem isOpen_localLogDomain (a : ℂ) : IsOpen (localLogDomain a) := by
  exact Complex.isOpen_slitPlane.preimage (continuous_id.div_const a)

/-- 当 `a ≠ 0` 时，基点 `a` 属于其局部对数定义域。-/
theorem mem_localLogDomain_center {a : ℂ} (ha : a ≠ 0) : a ∈ localLogDomain a := by
  change a / a ∈ Complex.slitPlane
  simpa only [div_self ha] using Complex.one_mem_slitPlane

/-- 局部对数分支在它的定义域上全纯。
> **Entry**: complex-analysis.holomorphic.elementary-/
theorem localLog_holomorphicOn (a : ℂ) :
    HolomorphicOnTextbook (localLogAt a) (localLogDomain a) := by
  rw [holomorphicOnTextbook_iff_forall_differentiableAt]
  intro z hz
  apply DifferentiableAt.add_const
  exact (Complex.differentiableAt_log hz).comp z
    (differentiableAt_id.div_const a)

/-- 局部对数分支确实是复指数在该域上的右逆。
> **Entry**: complex-analysis.holomorphic.elementary-/
theorem exp_localLogAt {a z : ℂ} (ha : a ≠ 0) (hz : z ∈ localLogDomain a) :
    Complex.exp (localLogAt a z) = z := by
  change Complex.exp (Complex.log (z / a) + Complex.log a) = z
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hz), Complex.exp_log ha]
  exact div_mul_cancel₀ z ha

end SandronesLibrary.ComplexAnalysis
