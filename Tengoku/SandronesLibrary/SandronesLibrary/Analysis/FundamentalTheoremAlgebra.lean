/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.Complex
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analysis / FundamentalTheoremAlgebra —— 代数学基本定理

本文件证明每个非常数复多项式存在复根，并由此推出复数域代数闭以及复多项式完全
分裂。矩阵的应用放在依赖本文件的 `LinearAlgebra/JordanSimilarity.lean` 中。
-/

namespace SandronesLibrary.Analysis.Complex

open Polynomial

/-- 代数学基本定理：每个非常数复系数多项式至少有一个复根。

> **Entry**: analysis.complex.fundamental-theorem-algebra-/
theorem fundamental_theorem_of_algebra {p : ℂ[X]} (hp : 0 < p.degree) :
    ∃ z : ℂ, p.eval z = 0 := by
  obtain ⟨z, hz⟩ := _root_.Complex.exists_root hp
  exact ⟨z, hz⟩

/-- 复数域是代数闭域。-/
theorem complex_is_algebraically_closed : IsAlgClosed ℂ := by
  apply IsAlgClosed.of_exists_root ℂ
  intro p _hmonic hirr
  obtain ⟨z, hz⟩ := fundamental_theorem_of_algebra
    (degree_pos_of_irreducible hirr)
  exact ⟨z, hz⟩

/-- 每个复系数多项式都在复数域上完全分裂。-/
theorem complex_polynomial_splits (p : ℂ[X]) : p.Splits := by
  letI : IsAlgClosed ℂ := complex_is_algebraically_closed
  exact IsAlgClosed.splits p

/-- 复多项式分解为首项系数乘以全部一次因子的乘积。-/
theorem complex_polynomial_eq_leadingCoeff_mul_prod_roots (p : ℂ[X]) :
    p = C p.leadingCoeff * (p.roots.map fun z => X - C z).prod := by
  exact (complex_polynomial_splits p).eq_prod_roots

end SandronesLibrary.Analysis.Complex
