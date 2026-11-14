/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.Complex.Conformal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cauchy–Riemann 方程

本文件当前条目：

- `complex-analysis.holomorphic.cauchy-riemann`：用四个实偏导定义 CR 方程，并证明必要性；
- `complex-analysis.holomorphic.cr-sufficient`：实 Fréchet 可微加 CR 推出复可微。

设 `f=u+iv`。我们把 `f` 看成实向量空间之间的映射，实 Fréchet 导数沿 `1` 与 `I`
的值分别是 x、y 方向导数；取其实部与虚部得到 `uₓ,uᵧ,vₓ,vᵧ`。公开定义由此写成
教材方程 `uₓ=vᵧ`、`uᵧ=-vₓ`。Mathlib 的“实导数尊重复标量乘法”只在证明中作桥。
-/

namespace SandronesLibrary.ComplexAnalysis

open Complex

noncomputable section

/-- `f=u+iv` 的实部 `u` 在 `z` 的 x 方向偏导候选，即实 Fréchet 导数沿向量 `1`
的值的实部。在本文件主定理的实可微前提下，它就是通常的偏导 `uₓ`。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann-/
def realPartPartialX (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ f z 1).re

/-- `f=u+iv` 的实部 `u` 在 `z` 的 y 方向偏导候选，即实 Fréchet 导数沿向量 `I`
的值的实部。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann-/
def realPartPartialY (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ f z I).re

/-- `f=u+iv` 的虚部 `v` 在 `z` 的 x 方向偏导候选，即实 Fréchet 导数沿向量 `1`
的值的虚部。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann-/
def imaginaryPartPartialX (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ f z 1).im

/-- `f=u+iv` 的虚部 `v` 在 `z` 的 y 方向偏导候选，即实 Fréchet 导数沿向量 `I`
的值的虚部。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann-/
def imaginaryPartPartialY (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ f z I).im

/-- **Cauchy–Riemann 方程**：`uₓ=vᵧ` 且 `uᵧ=-vₓ`。

该谓词只记录实导数候选满足的代数方程。由于 `fderiv` 在不可微处取默认值，使用它推出
复可微时必须另给 `DifferentiableAt ℝ f z`；本文件的充分性定理显式保留这一前提。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann-/
def SatisfiesCauchyRiemannAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  realPartPartialX f z = imaginaryPartPartialY f z ∧
    realPartPartialY f z = -imaginaryPartPartialX f z

/-- 两条坐标 CR 方程恰好表示实 Fréchet 导数尊重乘以 `I`：`L(I)=I·L(1)`。
这是本库教材坐标定义与 Mathlib 复线性导数后端之间的显式桥。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann
@isnad1 id=iff.0h2v.s9.e105df7791cc from=translated src=- shape=596f1603 vocab=d7830ef8
-/
theorem cauchyRiemann_iff_realFDeriv_map_I (f : ℂ → ℂ) (z : ℂ) :
    SatisfiesCauchyRiemannAt f z ↔
      fderiv ℝ f z I = I * fderiv ℝ f z 1 := by
  constructor
  · rintro ⟨huxvy, huyvx⟩
    apply Complex.ext
    · simpa [realPartPartialY, imaginaryPartPartialX] using huyvx
    · simpa [realPartPartialX, imaginaryPartPartialY] using huxvy.symm
  · intro h
    constructor
    · have him := congrArg Complex.im h
      simpa [realPartPartialX, imaginaryPartPartialY] using him.symm
    · have hre := congrArg Complex.re h
      simpa [realPartPartialY, imaginaryPartPartialX] using hre

/-- **Cauchy–Riemann 方程的必要性**：若 `f` 按本库差商定义在 `z` 复可微，则它作为
实平面映射在该点实 Fréchet 可微，并满足 `uₓ=vᵧ`、`uᵧ=-vₓ`。
> **Entry**: complex-analysis.holomorphic.cauchy-riemann
@isnad1 id=and.1h2v.s6.563f63aa42a9 from=translated src=- shape=b2206f4b vocab=10f6cc89
-/
theorem complexDifferentiableAt_cauchyRiemann {f : ℂ → ℂ} {z : ℂ}
    (hf : ComplexDifferentiableAtTextbook f z) :
    DifferentiableAt ℝ f z ∧ SatisfiesCauchyRiemannAt f z := by
  have hf' : DifferentiableAt ℂ f z :=
    complexDifferentiableAtTextbook_iff_differentiableAt.mp hf
  obtain ⟨hreal, hmap⟩ := differentiableAt_complex_iff_differentiableAt_real.mp hf'
  refine ⟨hreal, (cauchyRiemann_iff_realFDeriv_map_I f z).mpr ?_⟩
  simpa [smul_eq_mul] using hmap

/-- **Cauchy–Riemann 方程的充分性**：实 Fréchet 可微且满足 CR 方程的函数，按本库
差商定义在该点复可微。实可微性把两个方向等式提升为统一的一阶近似，不能省略。
> **Entry**: complex-analysis.holomorphic.cr-sufficient
@isnad1 id=complexd.2h2v.s6.6fe0fc90fa7d from=translated src=- shape=6399f6bc vocab=10f6cc89
-/
theorem complexDifferentiableAt_of_realDifferentiableAt_cauchyRiemann
    {f : ℂ → ℂ} {z : ℂ} (hreal : DifferentiableAt ℝ f z)
    (hcr : SatisfiesCauchyRiemannAt f z) :
    ComplexDifferentiableAtTextbook f z := by
  apply complexDifferentiableAtTextbook_iff_differentiableAt.mpr
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  exact ⟨hreal, by
    simpa [smul_eq_mul] using (cauchyRiemann_iff_realFDeriv_map_I f z).mp hcr⟩

/-- 在充分性定理的条件下，复导数等于实 Fréchet 导数沿 x 方向 `1` 的值，亦即
`uₓ+i vₓ`。本定理给出导数值而不只给出复可微性的存在结论。
> **Entry**: complex-analysis.holomorphic.cr-sufficient
@isnad1 id=hasderiv.2h2v.s9.99e14ccc3de4 from=translated src=- shape=f47f922b vocab=d972a559
-/
theorem hasComplexDerivAt_of_realDifferentiableAt_cauchyRiemann
    {f : ℂ → ℂ} {z : ℂ} (hreal : DifferentiableAt ℝ f z)
    (hcr : SatisfiesCauchyRiemannAt f z) :
    HasDerivAt f (fderiv ℝ f z 1) z := by
  have hmap : fderiv ℝ f z I = I • fderiv ℝ f z 1 := by
    simpa [smul_eq_mul] using (cauchyRiemann_iff_realFDeriv_map_I f z).mp hcr
  simpa using complexOfReal_hasDerivAt hreal hmap

end
end SandronesLibrary.ComplexAnalysis
