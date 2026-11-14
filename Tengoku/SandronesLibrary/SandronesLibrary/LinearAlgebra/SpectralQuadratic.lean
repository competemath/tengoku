/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.InnerProduct
import Tengoku.Seed.Analysis.InnerProductSpace.Spectrum
import Tengoku.Seed.LinearAlgebra.QuadraticForm.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / SpectralQuadratic —— 实谱定理、二次型与惯性定律

本文件给出有限维实内积空间中自伴算子的标准正交特征基，并将其对应二次型写成无
交叉项的平方和。随后给出 Sylvester 惯性定律：任意有限维实二次型都可化为系数为
`-1, 0, 1` 的标准形，而且正、负系数的个数与所选坐标无关。

公开陈述使用基、正交、特征向量、二次型和惯性指数等教材语言；更一般的子模语言
仅留在 mathlib 的证明实现中。

> **Entry**: linear-algebra.spectral-quadratic
-/

namespace SandronesLibrary.LinearAlgebra.SpectralQuadratic

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance : LinearSpace ℝ E where
  toModule := inferInstance

/-- 有限维实谱定理的教材形式：自伴算子存在标准正交特征基。
@isnad1 id=ex.2h3v.s8.a5885a9d5e46 from=translated src=- shape=0162caaa vocab=e4daa53e
-/
theorem spectral_theorem {n : ℕ} [FiniteDimensional ℝ E]
    (hn : dim ℝ E = n) (T : E →ₗ[ℝ] E)
    (hT : IsSelfAdjointOperator T) :
    ∃ (b : Fin n → E) (μ : Fin n → ℝ),
      IsBasis ℝ b ∧ Orthonormal ℝ b ∧
        ∀ i, T (b i) = μ i • b i := by
  have hTs : T.IsSymmetric := hT
  let B := hTs.eigenvectorBasis hn
  refine ⟨B, hTs.eigenvalues hn, ?_, B.orthonormal, ?_⟩
  · exact ⟨B.toBasis.linearIndependent, B.toBasis.span_eq⟩
  · intro i
    exact hTs.apply_eigenvectorBasis hn i

/-- 自伴算子对应的二次型。-/
def operatorQuadraticForm (T : E →ₗ[ℝ] E) (x : E) : ℝ :=
  inner ℝ (T x) x

/-- 在标准正交特征基下，二次型没有交叉项。
@isnad1 id=eq.2h6v.s8.77c82f9a1dcc from=translated src=- shape=c89e4f60 vocab=234b10ca
-/
theorem operatorQuadraticForm_diagonal {n : ℕ} (T : E →ₗ[ℝ] E)
    (b : Fin n → E) (μ c : Fin n → ℝ)
    (hb : Orthonormal ℝ b) (hTb : ∀ i, T (b i) = μ i • b i) :
    operatorQuadraticForm T (∑ i, c i • b i) =
      ∑ i, μ i * (c i) ^ 2 := by
  have hmap : T (∑ i, c i • b i) = ∑ i, (c i * μ i) • b i := by
    simp_rw [map_sum, map_smul, hTb, smul_smul]
  rw [operatorQuadraticForm, hmap]
  rw [show (∑ i, (c i * μ i) • b i) =
      ∑ i ∈ Finset.univ, (c i * μ i) • b i by simp]
  rw [show (∑ i, c i • b i) = ∑ i ∈ Finset.univ, c i • b i by simp]
  rw [hb.inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

section Inertia

variable {V : Type*} [AddCommGroup V] [LinearSpace ℝ V]
  [IsFiniteDimensional ℝ V]

/-- 二次型 `Q` 等价于权重为 `w` 的平方和。-/
def IsDiagonalForm (Q : QuadraticForm ℝ V)
    (w : Fin (dim ℝ V) → ℝ) : Prop :=
  QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w)

/-- 二次型的正惯性指数。-/
noncomputable def positiveIndex (Q : QuadraticForm ℝ V) : ℕ :=
  sigPos Q

/-- 二次型的负惯性指数。-/
noncomputable def negativeIndex (Q : QuadraticForm ℝ V) : ℕ :=
  sigNeg Q

/-- Sylvester 惯性定律的存在部分：任意有限维实二次型都等价于系数仅为
`-1, 0, 1` 的平方和。
@isnad1 id=ex.0h2v.s6.1a8d6be7f85e from=translated src=- shape=8b3cdda6 vocab=33466d1d
-/
theorem inertia_normal_form (Q : QuadraticForm ℝ V) :
    ∃ w : Fin (dim ℝ V) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ IsDiagonalForm Q w := by
  simpa [IsDiagonalForm, dim] using
    Q.equivalent_one_zero_neg_one_weighted_sum_squared

/-- Sylvester 惯性定律的唯一性部分：任何对角表示中正系数和负系数的个数
只由二次型本身决定。
@isnad1 id=and.1h3v.s7.945c03913dd9 from=translated src=- shape=91169d89 vocab=1c02b55f
-/
theorem inertia_indices_unique (Q : QuadraticForm ℝ V)
    (w : Fin (dim ℝ V) → ℝ) (hw : IsDiagonalForm Q w) :
    positiveIndex Q = Set.ncard {i | 0 < w i} ∧
      negativeIndex Q = Set.ncard {i | w i < 0} := by
  change sigPos Q = Set.ncard {i | 0 < w i} ∧
    sigNeg Q = Set.ncard {i | w i < 0}
  exact ⟨QuadraticForm.sigPos_of_equiv_weightedSumSquares hw,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw⟩

end Inertia

end SandronesLibrary.LinearAlgebra.SpectralQuadratic
