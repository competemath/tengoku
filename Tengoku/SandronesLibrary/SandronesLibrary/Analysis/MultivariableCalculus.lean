/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.NormedSpace
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Matrix
import Tengoku.Seed.Algebra.BigOperators.Pi
import Tengoku.Seed.Analysis.Calculus.FDeriv.Comp
import Tengoku.Seed.Analysis.Calculus.FDeriv.Symmetric
import Tengoku.Seed.Analysis.Calculus.Gradient.Basic
import Tengoku.Seed.Analysis.Calculus.LineDeriv.Basic
import Tengoku.Seed.Analysis.Calculus.TaylorIntegral
import Tengoku.Seed.Data.Matrix.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 多元微积分：Fréchet 全微分、方向导数与梯度

多元函数在一点的最佳线性近似不是一个数，而是连续线性映射。若
`f(x+h)=f(x)+A(h)+o(‖h‖)`，则 `A` 是 `f` 在 `x` 处的 Fréchet 导数，也就是教材
中的全微分。将 `A` 作用于方向 `v` 得到该方向上的方向导数。

对实内积空间上的实值函数，Riesz 表示把线性泛函 `A` 唯一写成
`A(v)=⟪∇f(x),v⟫`；这个代表向量就是梯度。本模块建立这些概念之间的统一接口，
并给出连续性、恒等映射和链式法则。坐标偏导、Jacobian 与 Hessian 将在后续小节
由这一无坐标定义推出。
-/

namespace SandronesLibrary.Analysis.Multivariable

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- 教材中的全微分：定义域到值域的连续实线性映射。

> **Entry**: analysis.multivariable.frechet-/
abbrev TotalDerivative := E →L[ℝ] F

/-- `A` 是 `f` 在 `x` 处 Fréchet 导数的教材余项比值定义。-/
def HasFrechetDerivativeAtTextbook (f : E → F) (A : TotalDerivative (E := E) (F := F))
    (x : E) : Prop :=
  Filter.Tendsto (fun y => ‖y - x‖⁻¹ * ‖f y - f x - A (y - x)‖)
    (nhds x) (nhds 0)

/-- 本库余项比值定义与 Mathlib 的 `HasFDerivAt` 完全等价。
@isnad1 id=iff.0h5v.s6.a093cd3d45a8 from=translated src=- shape=fb3f1d81 vocab=362362e0
-/
theorem hasFrechetDerivativeAtTextbook_iff_hasFDerivAt
    {f : E → F} {A : TotalDerivative (E := E) (F := F)} {x : E} :
    HasFrechetDerivativeAtTextbook f A x ↔ HasFDerivAt f A x := by
  exact (hasFDerivAt_iff_tendsto (f := f) (f' := A) (x := x)).symm

/-- 教材余项接口下 Fréchet 导数唯一。
@isnad1 id=eq.2h6v.s6.e2e15c88cbc3 from=translated src=- shape=af9795d6 vocab=ee518173
-/
theorem hasFrechetDerivativeAtTextbook_unique
    {f : E → F} {A B : TotalDerivative (E := E) (F := F)} {x : E}
    (hA : HasFrechetDerivativeAtTextbook f A x)
    (hB : HasFrechetDerivativeAtTextbook f B x) : A = B := by
  exact (hasFrechetDerivativeAtTextbook_iff_hasFDerivAt.mp hA).unique
    (hasFrechetDerivativeAtTextbook_iff_hasFDerivAt.mp hB)

/-- `d` 是 `f` 在 `x` 沿方向 `v` 的教材方向导数：当非零实数 `t` 趨于零时，
方向差商趋于 `d`。这只检查一个固定方向，严格弱于 Fréchet 可微性。-/
def HasDirectionalDerivativeAtTextbook (f : E → F) (d : F) (x v : E) : Prop :=
  Filter.Tendsto (fun t : ℝ ↦ t⁻¹ • (f (x + t • v) - f x)) (nhdsWithin 0 {0}ᶜ) (nhds d)

/-- 教材方向差商定义与 Mathlib 的沿直线导数谓词完全等价。
@isnad1 id=iff.0h6v.s6.c12ae25079e5 from=translated src=- shape=f448033d vocab=3ae8c934
-/
theorem hasDirectionalDerivativeAtTextbook_iff_hasLineDerivAt
    {f : E → F} {d : F} {x v : E} :
    HasDirectionalDerivativeAtTextbook f d x v ↔ HasLineDerivAt ℝ f d x v := by
  exact hasLineDerivAt_iff_tendsto_slope_zero.symm

/-- 固定点和方向上的教材方向导数唯一。
@isnad1 id=eq.2h7v.s6.932d905cc27d from=translated src=- shape=10396d9d vocab=f228a67b
-/
theorem hasDirectionalDerivativeAtTextbook_unique
    {f : E → F} {d₁ d₂ : F} {x v : E}
    (h₁ : HasDirectionalDerivativeAtTextbook f d₁ x v)
    (h₂ : HasDirectionalDerivativeAtTextbook f d₂ x v) : d₁ = d₂ := by
  exact (hasDirectionalDerivativeAtTextbook_iff_hasLineDerivAt.mp h₁).unique
    (hasDirectionalDerivativeAtTextbook_iff_hasLineDerivAt.mp h₂)

/-- Fréchet 可微蕴含每个固定方向上的教材方向导数，导数值为 `A v`。
反向一般不成立，因此这里只提供单向桥。
@isnad1 id=hasdirec.1h6v.s7.6a751dc7b9a0 from=translated src=- shape=a2492cd6 vocab=d98913d4
-/
theorem frechetDerivativeTextbook_hasDirectionalDerivativeAtTextbook
    {f : E → F} {A : TotalDerivative (E := E) (F := F)} {x v : E}
    (h : HasFrechetDerivativeAtTextbook f A x) :
    HasDirectionalDerivativeAtTextbook f (A v) x v := by
  rw [hasDirectionalDerivativeAtTextbook_iff_hasLineDerivAt]
  exact (hasFrechetDerivativeAtTextbook_iff_hasFDerivAt.mp h).hasLineDerivAt v

/-- 方向导数取 Fréchet 导数在线性方向 `v` 上的值。不可微时 Mathlib 的 `fderiv`
按约定取零，因此需要实际计算时通常同时携带 `HasFDerivAt` 假设。-/
noncomputable def DirectionalDerivative (f : E → F) (x v : E) : F :=
  fderiv ℝ f x v

/-- 已知的全微分等于 Mathlib 选出的 Fréchet 导数。
@isnad1 id=eq.1h5v.s8.6738b15a8bdb from=translated src=- shape=b7e576c4 vocab=e7d5b0f3
-/
theorem totalDerivative_unique {f : E → F} {x : E} {A : E →L[ℝ] F}
    (h : HasFDerivAt f A x) : fderiv ℝ f x = A := by
  exact h.fderiv

/-- Fréchet 可微蕴含在该点连续。
@isnad1 id=continuo.1h4v.s6.72c0db370863 from=translated src=- shape=e0d20722 vocab=6bdf1193
-/
theorem differentiable_continuousAt {f : E → F} {x : E}
    (h : DifferentiableAt ℝ f x) : ContinuousAt f x := by
  exact h.continuousAt

/-- 恒等映射的全微分是恒等连续线性映射。
@isnad1 id=hasfderi.0h2v.s6.e8846c44f233 from=translated src=- shape=b186a30b vocab=4644dba2
-/
theorem totalDerivative_id (x : E) :
    HasFDerivAt id (ContinuousLinearMap.id ℝ E) x := by
  exact hasFDerivAt_id x

/-- **多元链式法则**：复合函数的全微分是两个全微分的复合。
@isnad1 id=hasfderi.2h8v.s8.046647f48c1f from=translated src=- shape=9cdd0d8b vocab=5ef388df
-/
theorem totalDerivative_chain {f : E → F} {g : F → G}
    {x : E} {A : E →L[ℝ] F} {B : F →L[ℝ] G}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B (f x)) :
    HasFDerivAt (g ∘ f) (B.comp A) x := by
  exact hg.comp x hf

/-- 可微时，方向导数就是全微分作用于方向向量。
@isnad1 id=eq.1h6v.s8.21d75346ab9d from=translated src=- shape=1f0d3781 vocab=4c757bb9
-/
theorem directionalDerivative_eq {f : E → F} {x v : E} {A : E →L[ℝ] F}
    (h : HasFDerivAt f A x) : DirectionalDerivative f x v = A v := by
  simp [DirectionalDerivative, h.fderiv]

section Gradient

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- 梯度通过内积给出实值函数的全微分。

> **Entry**: analysis.multivariable.gradient
@isnad1 id=hasfderi.1h4v.s10.df31f3d0c968 from=translated src=- shape=ca080452 vocab=09f22c8b
-/
theorem gradient_totalDerivative {f : H → ℝ} {x grad : H}
    (h : HasGradientAt f grad x) :
    HasFDerivAt f (InnerProductSpace.toDual ℝ H grad) x := by
  exact h.hasFDerivAt

/-- **方向导数—梯度公式**：`D_v f(x)=⟪∇f(x),v⟫`。
@isnad1 id=eq.1h5v.s6.bb583bd4f06e from=translated src=- shape=7053fffc vocab=354f1bc1
-/
theorem directionalDerivative_eq_inner_gradient {f : H → ℝ} {x grad v : H}
    (h : HasGradientAt f grad x) :
    DirectionalDerivative f x v = inner ℝ grad v := by
  simpa [DirectionalDerivative] using h.fderiv_apply (y := v)

end Gradient

section Coordinates

open scoped BigOperators Matrix

/-!
## 坐标偏导与 Jacobian

以下固定定义域为 `ℝⁿ = Fin n → ℝ`、值域为 `ℝᵐ = Fin m → ℝ`。第 `j` 个标准基
向量写作 `Pi.single j 1`。全微分作用于这个向量就得到第 `j` 个坐标方向的偏导向量；
再取其第 `i` 个分量，便得到教材中的 `∂fᵢ/∂xⱼ`。将这些数按“输出分量为行、输入
变量为列”排列，就得到 `m × n` Jacobian 矩阵。
-/

/-- 第 `j` 个坐标方向的偏导向量。由于它由 `fderiv` 定义，不可微点按 Mathlib 的约定
取零；具体计算时应携带 `HasFDerivAt` 假设。-/
noncomputable def partialDerivative {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (x : Fin n → ℝ) (j : Fin n) : Fin m → ℝ :=
  DirectionalDerivative f x (Pi.single j 1)

/-- `f : ℝⁿ → ℝᵐ` 在 `x` 处的 Jacobian 矩阵。矩阵第 `i,j` 项是输出分量 `fᵢ`
对输入坐标 `xⱼ` 的偏导数。-/
noncomputable def jacobian {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j ↦ partialDerivative f x j i

/-- 已知 Fréchet 导数 `A` 时，第 `j` 个偏导向量就是 `A eⱼ`。

> **Entry**: analysis.multivariable.coordinates
@isnad1 id=eq.1h6v.s8.0fb8b41a809c from=translated src=- shape=e12e25c2 vocab=97b6839a
-/
theorem partialDerivative_eq {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {x : Fin n → ℝ} {A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)}
    (h : HasFDerivAt f A x) (j : Fin n) :
    partialDerivative f x j = A (Pi.single j 1) := by
  exact directionalDerivative_eq h

/-- Jacobian 元素公式：`Jf(x)ᵢⱼ = (Df(x)eⱼ)ᵢ`。
@isnad1 id=eq.1h7v.s8.12aafa940e61 from=translated src=- shape=a61cc020 vocab=8f72c5ab
-/
theorem jacobian_apply {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {x : Fin n → ℝ} {A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)}
    (h : HasFDerivAt f A x) (i : Fin m) (j : Fin n) :
    jacobian f x i j = A (Pi.single j 1) i := by
  rw [jacobian, partialDerivative_eq h]

/-- **全微分的 Jacobian 表示**：在标准坐标中，全微分作用于向量 `v` 等于
Jacobian 矩阵乘以列向量 `v`。这是抽象 Fréchet 导数与教材矩阵记法之间的桥。
@isnad1 id=eq.1h6v.s8.75978ab82314 from=translated src=- shape=92027ef1 vocab=73d978a6
-/
theorem totalDerivative_apply_eq_jacobian_mulVec {n m : ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} {x v : Fin n → ℝ}
    {A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)} (h : HasFDerivAt f A x) :
    A v = jacobian f x *ᵥ v := by
  classical
  have hb (j : Fin n) : (fun k ↦ if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext k
    simp [Pi.single_apply, eq_comm]
  have hA : A v = ∑ j, v j • A (Pi.single j 1) := by
    change A.toLinearMap v = ∑ j, v j • A.toLinearMap (Pi.single j 1)
    simpa only [hb] using A.toLinearMap.pi_apply_eq_sum_univ v
  rw [hA]
  ext i
  simp [Matrix.mulVec, dotProduct, jacobian_apply h, mul_comm]

/-- 恒等映射在任意点的 Jacobian 都是单位矩阵。
@isnad1 id=eq.0h2v.s5.84d786f57b89 from=translated src=- shape=8e52d387 vocab=2b9724de
-/
theorem jacobian_id {n : ℕ} (x : Fin n → ℝ) :
    jacobian id x = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext i j
  rw [jacobian_apply (totalDerivative_id x)]
  simp [Pi.single_apply, Matrix.one_apply]

/-- **Jacobian 链式法则**：复合映射的 Jacobian 是两个 Jacobian 的矩阵乘积。
矩阵次序与函数复合次序相反：先作用 `Jf(x)`，再作用 `Jg(f(x))`。
@isnad1 id=eq.2h8v.s8.a19461cf7374 from=translated src=- shape=b753e217 vocab=65c5bde0
-/
theorem jacobian_chain {n m p : ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x : Fin n → ℝ}
    {A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)}
    {B : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B (f x)) :
    jacobian (g ∘ f) x = jacobian g (f x) * jacobian f x := by
  classical
  have hc : HasFDerivAt (g ∘ f) (B.comp A) x := totalDerivative_chain hf hg
  ext i j
  rw [jacobian_apply hc, Matrix.mul_apply]
  change B (A (Pi.single j 1)) i = _
  rw [congrFun (totalDerivative_apply_eq_jacobian_mulVec hg
    (v := A (Pi.single j 1))) i]
  simp [Matrix.mulVec, dotProduct, jacobian_apply hf]

end Coordinates

section HessianTaylor

/-!
## Hessian 与任意阶多元 Taylor 公式

对实值函数 `f : ℝⁿ → ℝ`，二阶 Fréchet 导数是连续双线性型。在标准基上计算该
双线性型，得到 Hessian 矩阵。二阶连续可微保证混合偏导可以交换，因此 Hessian 对称。

多元 Taylor 公式沿线段 `t ↦ x + t • y` 化为单变量公式。`iteratedFDeriv ℝ k f x`
是 `k` 重连续多线性映射；把它的每个输入都取为位移 `y`，便得到齐次 `k` 次项。
下方公式保留任意阶数和积分型余项，不依赖无穷级数，也不要求函数解析。
-/

/-- 实值函数在标准坐标下的 Hessian 矩阵。第 `i,j` 项是二阶 Fréchet 导数在标准
基向量 `eᵢ,eⱼ` 上的值，也就是教材记号 `∂²f/∂xᵢ∂xⱼ`。-/
noncomputable def hessian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1]

/-- 沿位移 `y` 计算的 `N` 阶多元 Taylor 多项式：
`Σₖ₌₀ᴺ Dᵏf(x)[y,…,y]/k!`。-/
noncomputable def multivariableTaylorPolynomial {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : ℕ) (f : E → F) (x y : E) : F :=
  ∑ k ∈ Finset.range (N + 1), (Nat.factorial k : ℝ)⁻¹ •
    iteratedFDeriv ℝ k f x (fun _ ↦ y)

/-- **Hessian 对称性**：若 `f` 在 `x` 处二阶连续可微，则 Hessian 是对称矩阵。
这就是混合偏导交换定理在标准坐标中的矩阵形式。

> **Entry**: analysis.multivariable.hessian-taylor
@isnad1 id=issymmet.1h3v.s6.b2f96500d415 from=translated src=- shape=e6915041 vocab=0e80aec8
-/
theorem hessian_symmetric {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    SandronesLibrary.LinearAlgebra.Matrix.IsSymmetric (hessian f x) := by
  rw [SandronesLibrary.LinearAlgebra.Matrix.isSymmetric_iff_mathlib]
  apply Matrix.IsSymm.ext
  intro i j
  simpa [hessian] using
    (hf.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons
      (v := Pi.single j 1) (w := Pi.single i 1)

/-- **任意阶多元 Taylor 公式（积分型余项）**。若 `f` 沿 `x` 到 `x+y` 的线段
处处 `Cᴺ⁺¹`，则函数值等于 `N` 阶 Taylor 多项式加上
`1/N! ∫₀¹ (1-t)ᴺ Dᴺ⁺¹f(x+ty)[y,…,y] dt`。

公式对一般实赋范空间到完备实赋范空间的映射成立；有限维多元函数只是其特例。
@isnad1 id=eq.1h6v.s9.0efaf5b8ece9 from=translated src=- shape=3b57d369 vocab=1c8dc84e
-/
theorem multivariable_taylor_integral_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {N : ℕ} {f : E → F} {x y : E}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (N + 1) f (x + t • y)) :
    f (x + y) = multivariableTaylorPolynomial N f x y +
      (Nat.factorial N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
        (1 - t) ^ N • iteratedFDeriv ℝ (N + 1) f (x + t • y) (fun _ ↦ y) := by
  simpa [multivariableTaylorPolynomial] using
    (map_add_eq_sum_add_integral_iteratedFDeriv (n := N) hf)

/-- Taylor 积分余项公式的零阶（亦即一阶微积分基本定理）特例：函数增量等于
全微分沿连接线段的积分。该公式也是多元 Taylor 定理归约到线段的最基本情形。
@isnad1 id=eq.1h5v.s9.9be3b81b4e56 from=translated src=- shape=8866df5e vocab=74e76939
-/
theorem multivariable_taylor_first_order {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x y : E}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f (x + t • y)) :
    f (x + y) = f x + ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • y) y := by
  simpa [multivariableTaylorPolynomial, iteratedFDeriv_one_apply] using
    (multivariable_taylor_integral_remainder (N := 0) hf)

end HessianTaylor

end SandronesLibrary.Analysis.Multivariable
