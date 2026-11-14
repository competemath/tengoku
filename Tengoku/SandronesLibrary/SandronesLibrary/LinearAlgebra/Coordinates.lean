/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.LinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / Coordinates —— 坐标、过渡矩阵与换基公式

设 `b` 与 `b'` 是有限维向量空间的两组有序基。本文件建立教材中的以下链条：

* `coordinates b hb x` 是向量 `x` 在基 `b` 下的坐标；
* `transitionMatrix b b' hb hb'` 把 `b`-坐标变成 `b'`-坐标；
* 两个方向的过渡矩阵互逆；
* 同一线性算子在不同基下的矩阵由过渡矩阵作相似变换得到。

公开签名只使用本库教材层的 `LinearSpace`、`IsBasis`、坐标函数与矩阵。
mathlib 的模、基及矩阵表示接口只在定义体和证明内部承担实现工作。

> **Entry**: linear-algebra.coordinates.change-basis
-/

namespace SandronesLibrary.LinearAlgebra.Coordinates

open SandronesLibrary.LinearAlgebra.VectorSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 向量 `x` 在基 `b` 下的坐标。证明 `hb` 保证每个向量有唯一坐标。-/
noncomputable def coordinates (b : ι → V) (hb : IsBasis K b) (x : V) : ι → K := by
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  exact fun i => B.repr x i

/-- 从基 `b` 的坐标变到基 `b'` 的坐标的过渡矩阵。
其第 `j` 列是旧基向量 `b j` 在新基 `b'` 下的坐标。-/
noncomputable def transitionMatrix (b b' : ι → V) (hb : IsBasis K b)
    (hb' : IsBasis K b') : Matrix ι ι K := by
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' := Module.Basis.mk hb'.1 (by simpa [hb'.2])
  exact B'.toMatrix B

/-- **坐标换基公式**：左乘过渡矩阵，把 `x` 的旧坐标变为新坐标。-/
theorem transitionMatrix_mulVec_coordinates (b b' : ι → V) (hb : IsBasis K b)
    (hb' : IsBasis K b') (x : V) :
    Matrix.mulVec (transitionMatrix b b' hb hb') (coordinates b hb x) =
      coordinates b' hb' x := by
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' := Module.Basis.mk hb'.1 (by simpa [hb'.2])
  simpa [coordinates, transitionMatrix, B, B'] using
    (Module.Basis.toMatrix_mulVec_repr B B' x)

/-- 反向换基矩阵是正向换基矩阵的右逆。-/
theorem transitionMatrix_mul_reverse (b b' : ι → V) (hb : IsBasis K b)
    (hb' : IsBasis K b') :
    transitionMatrix b b' hb hb' * transitionMatrix b' b hb' hb = 1 := by
  classical
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' := Module.Basis.mk hb'.1 (by simpa [hb'.2])
  simpa [transitionMatrix, B, B'] using
    (Module.Basis.toMatrix_mul_toMatrix_flip B' B)

/-- 反向换基矩阵也是正向换基矩阵的左逆。-/
theorem reverse_mul_transitionMatrix (b b' : ι → V) (hb : IsBasis K b)
    (hb' : IsBasis K b') :
    transitionMatrix b' b hb' hb * transitionMatrix b b' hb hb' = 1 := by
  classical
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' := Module.Basis.mk hb'.1 (by simpa [hb'.2])
  simpa [transitionMatrix, B, B'] using
    (Module.Basis.toMatrix_mul_toMatrix_flip B B')

/-- 线性算子 `T` 在基 `b` 下的矩阵；第 `j` 列是 `T (b j)` 的 `b`-坐标。-/
noncomputable def operatorMatrix (b : ι → V) (hb : IsBasis K b)
    (T : V →ₗ[K] V) : Matrix ι ι K := by
  classical
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  exact LinearMap.toMatrix B B T

/-- **算子矩阵换基公式**：同一线性算子在两组基下的矩阵相似。

若 `P` 把 `b`-坐标变为 `b'`-坐标，则 `[T]_{b'} = P [T]_b P⁻¹`；
这里反方向的过渡矩阵直接充当 `P⁻¹`，无需另行引入矩阵求逆。-/
theorem operatorMatrix_change_basis (b b' : ι → V) (hb : IsBasis K b)
    (hb' : IsBasis K b') (T : V →ₗ[K] V) :
    operatorMatrix b' hb' T = transitionMatrix b b' hb hb' * operatorMatrix b hb T *
      transitionMatrix b' b hb' hb := by
  classical
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' := Module.Basis.mk hb'.1 (by simpa [hb'.2])
  simpa [operatorMatrix, transitionMatrix, B, B'] using
    (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix B' B B' B T).symm

end SandronesLibrary.LinearAlgebra.Coordinates
