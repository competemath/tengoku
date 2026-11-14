/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.LinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology
open scoped Filter Topology

/-!
# LinearAlgebra / Determinant —— 行列式（线性代数第一学期 L3）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **linear-algebra.det.mul**（积的行列式：det(AB) = det A · det B）。
* **linear-algebra.det.transpose**（转置不变：det Aᵀ = det A）。
* **linear-algebra.det.invertible**（可逆 ⟺ det ≠ 0：det 为可逆元 ⟹ 有逆）。
* **linear-algebra.det.one-zero**（单位阵 det=1，零阵 det=0）。

> **实现注记**：教材的"行列式 det"在形式化层即 `Matrix.det`；"det A ≠ 0"对应
> `IsUnit A.det`（域上二者等价）。词条用教材记号（det、可逆），mathlib 名只作实现注记。
-/

namespace SandronesLibrary

namespace LinearAlgebra.Determinant

/-- **积的行列式**：det(A·B) = det A · det B。 
> **Entry**: linear-algebra.det.mul
@isnad1 id=eq.0h4v.s6.c2353fecddf9 from=translated src=- shape=3fdeaf95 vocab=9683d45a
-/
theorem det_mul {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A B : Matrix n n K) : (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- **转置不变**：det(Aᵀ) = det A。 
> **Entry**: linear-algebra.det.transpose
@isnad1 id=eq.0h3v.s5.8882b6d91a52 from=translated src=- shape=99c1e1d4 vocab=2a5b4263
-/
theorem det_transpose {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) : A.transpose.det = A.det :=
  Matrix.det_transpose A

/-- **可逆 ⟺ det ≠ 0**：若 det A 是域上的可逆元（等价于 det A ≠ 0），
  则 A⁻¹ 给出左右逆：A⁻¹·A = 1 且 A·A⁻¹ = 1。 
> **Entry**: linear-algebra.det.invertible
@isnad1 id=and.1h3v.s7.7c12853b9ce8 from=translated src=- shape=27f2c3c0 vocab=7cfe7671
-/
theorem det_invertible {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (h : IsUnit A.det) :
    A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul A h, Matrix.mul_nonsing_inv A h⟩

/-- **单位阵的行列式**：det I = 1。 
> **Entry**: linear-algebra.det.one-zero
@isnad1 id=eq.0h2v.s6.b8f3ffdbec35 from=translated src=- shape=2f1fc875 vocab=a61e7bc9
-/
theorem det_one {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n] :
    (1 : Matrix n n K).det = 1 :=
  Matrix.det_one

/-- **零阵的行列式**：det 0 = 0（非平凡阶数）。 
> **Entry**: linear-algebra.det.one-zero
@isnad1 id=eq.0h2v.s6.1062fb675e8b from=translated src=- shape=7e3efd61 vocab=57c451f7
-/
theorem det_zero {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n] [Nonempty n] :
    (0 : Matrix n n K).det = 0 :=
  Matrix.det_zero

/-- **伴随矩阵**（教材记号）：`adj A` 是 A 的伴随矩阵（代数余子式矩阵的转置）。-/
abbrev adj (K : Type*) {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) : Matrix n n K :=
  A.adjugate

/-- **A·adj(A) = det A·I**：伴随矩阵的基本性质。 
> **Entry**: linear-algebra.det.adjugate
@isnad1 id=eq.0h3v.s7.c93adc162179 from=translated src=- shape=9654a013 vocab=d0022ee8
-/
theorem mul_adj {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) : A * adj K A = A.det • 1 := by
  unfold adj
  exact Matrix.mul_adjugate A

/-- **adj(A)·A = det A·I**。 
> **Entry**: linear-algebra.det.adjugate
@isnad1 id=eq.0h3v.s7.7829e06f766a from=translated src=- shape=5023830c vocab=d0022ee8
-/
theorem adj_mul {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) : adj K A * A = A.det • 1 := by
  unfold adj
  exact Matrix.adjugate_mul A

/-- **Cramer 法则（逐分量）**：AX = b 时，(A.cramer b) i 是把 A 的第 i 列换成 b 后的行列式。 
> **Entry**: linear-algebra.det.cramer
@isnad1 id=eq.0h5v.s8.0618b8353857 from=translated src=- shape=8793e33d vocab=b165b5d2
-/
theorem cramer_apply {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (b : n → K) (i : n) :
    (A.cramer b) i = (A.updateCol i b).det :=
  Matrix.cramer_apply A b i

/-- **Cramer 法则（解方程）**：A·(A.cramer b) = det A · b，故当 det A ≠ 0 时，
  x = (A.cramer b)/det A 是 AX = b 的唯一解。 
> **Entry**: linear-algebra.det.cramer
@isnad1 id=eq.0h4v.s8.5251414d71c9 from=translated src=- shape=5647cfd3 vocab=f82df4cc
-/
theorem cramer_solution {K : Type*} {n : Type*} [Field K] [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (b : n → K) : Matrix.mulVec A (A.cramer b) = A.det • b :=
  Matrix.mulVec_cramer A b

end LinearAlgebra.Determinant

end SandronesLibrary
