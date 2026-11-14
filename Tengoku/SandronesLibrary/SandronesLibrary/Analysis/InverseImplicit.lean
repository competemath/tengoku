/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.MultivariableCalculus
import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 多元反函数定理、隐函数定理与满秩秩定理

反函数定理研究导数可逆时函数本身的局部可逆性；隐函数定理研究方程
`f(x,y)=f(a,b)` 能否在局部唯一解出 `y=ψ(x)`；秩定理的满秩（次浸没）情形则把
正则水平集化为这种图像正规形。

本模块在实 Banach 空间上陈述这些结果。有限维欧氏空间自动满足完备性，因此教材中的
`ℝⁿ` 版本是直接特例。反函数定理要求全微分由连续线性同构给出；隐函数定理要求关于
第二组变量的偏全微分可逆。后者的导数公式为

`Dψ(a) = -(D₂f(a,b))⁻¹ ∘ D₁f(a,b)`。

最后一个定理是秩定理的满秩/次浸没形式。一般常秩 `r` 正规形还需要把定义域和值域
同时按核、像及补空间分解，Mathlib 当前没有直接的常秩定理接口，故在后续独立批次处理。
-/

namespace SandronesLibrary.Analysis.Multivariable

open Filter

/-- **多元反函数定理**。若 `f` 在 `a` 处 `C¹`，且全微分是连续线性同构 `L`，则
存在以 `f` 为正向映射的局部同胚；它包含 `a` 与 `f(a)`，局部逆仍为 `C¹`，并且
其在 `f(a)` 处的导数是 `L⁻¹`。

> **Entry**: analysis.multivariable.inverse-function
@isnad1 id=ex.2h5v.s9.9fedd67af243 from=translated src=- shape=9b4f53c1 vocab=1162d6a6
-/
theorem inverse_function_theorem {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {a : E} {L : E ≃L[ℝ] F}
    (hf : ContDiffAt ℝ 1 f a) (hL : HasFDerivAt f (L : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ a ∈ e.source ∧ f a ∈ e.target ∧
      ContDiffAt ℝ 1 e.symm (f a) ∧
      HasFDerivAt e.symm (L.symm : F →L[ℝ] E) (f a) := by
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let hs := hf.hasStrictFDerivAt' hL hn
  let e := hs.toOpenPartialHomeomorph f
  have ha : a ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hfa : f a ∈ e.target := hs.image_mem_toOpenPartialHomeomorph_target
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have heinv : e.symm (f a) = a := by
    rw [← he]
    exact e.left_inv ha
  refine ⟨e, he, ha, hfa, ?_, ?_⟩
  · apply e.contDiffAt_symm hfa
    · rw [heinv]
      simpa only [he] using hL
    · rw [heinv]
      simpa only [he] using hf
  · change HasFDerivAt (hs.localInverse f L a) (L.symm : F →L[ℝ] E) (f a)
    exact hs.to_localInverse.hasFDerivAt

/-- **多元隐函数定理**。若 `f(x,y)` 在 `u=(a,b)` 处 `C¹`，且关于 `y` 的偏全微分
`D₂f(u)` 可逆，则存在局部隐函数 `ψ`：它通过基点、局部满足原方程、仍为 `C¹`，
并满足标准导数公式 `Dψ=-(D₂f)⁻¹∘D₁f`。

> **Entry**: analysis.multivariable.implicit-function
@isnad1 id=ex.2h5v.s10.47b78de20435 from=translated src=- shape=1f40ab52 vocab=d574754b
-/
theorem implicit_function_theorem {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E₁ × E₂ → F} {u : E₁ × E₂}
    (hf : ContDiffAt ℝ 1 f u)
    (h₂ : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ → E₂,
      ψ u.1 = u.2 ∧
      (∀ᶠ x in nhds u.1, f (x, ψ x) = f u) ∧
      ContDiffAt ℝ 1 ψ u.1 ∧
      HasFDerivAt ψ
        (-(fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ E₁ E₂).inverse ∘L
          (fderiv ℝ f u ∘L ContinuousLinearMap.inl ℝ E₁ E₂)) u.1 := by
  let ψ := hf.implicitFunction (by norm_num) h₂
  refine ⟨ψ, hf.implicitFunction_apply_self (by norm_num) h₂,
    hf.eventually_apply_implicitFunction (by norm_num) h₂,
    hf.contDiffAt_implicitFunction (by norm_num) h₂, ?_⟩
  exact (hf.hasStrictFDerivAt_implicitFunction (by norm_num) h₂).hasFDerivAt

/-- **满秩秩定理（正则水平集正规形）**。在隐变量方向的偏全微分可逆时，水平集
`f(v)=f(u)` 在 `u` 的某个邻域内恰好是图像 `v₂=ψ(v₁)`。这给出秩等于值域维数时
秩定理的标准局部正规形，也是正则水平集定理的函数空间版本。

> **Entry**: analysis.multivariable.full-rank-theorem
@isnad1 id=ex.2h5v.s9.1b803c5269b8 from=translated src=- shape=cbc71f8d vocab=a6591abc
-/
theorem full_rank_level_set_normal_form {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E₁ × E₂ → F} {u : E₁ × E₂}
    (hf : ContDiffAt ℝ 1 f u)
    (h₂ : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧
      ∀ᶠ v in nhds u, (f v = f u ↔ ψ v.1 = v.2) := by
  exact ⟨hf.implicitFunction (by norm_num) h₂,
    hf.implicitFunction_apply_self (by norm_num) h₂,
    hf.eventually_apply_eq_iff_implicitFunction (by norm_num) h₂⟩

end SandronesLibrary.Analysis.Multivariable
