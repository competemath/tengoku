/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.VectorSpace
import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
import Tengoku.Seed.Analysis.InnerProductSpace.GramSchmidtOrtho
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / InnerProduct —— 内积、正交与 Gram–Schmidt

本文件建立有限维实内积空间的教材接口。公开陈述使用向量、内积、范数、线性无关和
基，不暴露 mathlib 更一般的模语言；证明内部调用其内积空间与 Gram–Schmidt 理论。

> **Entry**: linear-algebra.inner-product
-/

namespace SandronesLibrary.LinearAlgebra.InnerProduct

open SandronesLibrary.LinearAlgebra.VectorSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- 内积空间已经带有实向量空间结构；这里把它接到本库的教材包装。 -/
local instance : LinearSpace ℝ E where
  toModule := inferInstance

/-- 两个向量正交，意为它们的内积为零。-/
def AreOrthogonal (x y : E) : Prop := inner ℝ x y = 0

/-- 实内积空间中的 Cauchy–Schwarz 不等式。
@isnad1 id=le.0h3v.s5.fa3ae78d9242 from=translated src=- shape=23d428e3 vocab=26a1b885
-/
theorem cauchy_schwarz (x y : E) :
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ :=
  abs_real_inner_le_norm x y

/-- 向量与自身的内积等于范数平方。
@isnad1 id=eq.0h2v.s5.e3b80848f502 from=translated src=- shape=4ca600f4 vocab=d01ce673
-/
theorem inner_self_eq_norm_sq (x : E) :
    inner ℝ x x = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x

/-- 正交关系具有对称性。
@isnad1 id=iff.0h3v.s4.4f42858a4fb6 from=translated src=- shape=0e68a6f8 vocab=5bba0595
-/
theorem orthogonal_symm {x y : E} :
    AreOrthogonal x y ↔ AreOrthogonal y x := by
  exact inner_eq_zero_symm

/-- Gram–Schmidt 正交化后的向量组。-/
noncomputable def orthonormalize {n : ℕ} (v : Fin n → E) : Fin n → E :=
  InnerProductSpace.gramSchmidtNormed ℝ v

/-- 线性无关向量组经 Gram–Schmidt 后成为标准正交组。
@isnad1 id=orthonor.1h3v.s5.75240abf549a from=translated src=- shape=c05121b4 vocab=c2c3de74
-/
theorem orthonormalize_is_orthonormal {n : ℕ} {v : Fin n → E}
    (hv : IsLinearIndependent ℝ v) :
    Orthonormal ℝ (orthonormalize v) := by
  exact InnerProductSpace.gramSchmidtNormed_orthonormal hv

/-- Gram–Schmidt 保持线性无关性。
@isnad1 id=islinear.1h3v.s5.b00d244735a9 from=translated src=- shape=7745ab5a vocab=06ac82e6
-/
theorem orthonormalize_is_linearly_independent {n : ℕ} {v : Fin n → E}
    (hv : IsLinearIndependent ℝ v) :
    IsLinearIndependent ℝ (orthonormalize v) := by
  exact InnerProductSpace.gramSchmidtNormed_linearIndependent hv

/-- Gram–Schmidt 不改变原向量组张成的空间（仅供文件内部组装教材接口）。-/
private theorem orthonormalize_span_eq {n : ℕ} (v : Fin n → E) :
    Submodule.span ℝ (Set.range (orthonormalize v)) =
      Submodule.span ℝ (Set.range v) := by
  calc
    Submodule.span ℝ (Set.range (orthonormalize v)) =
        Submodule.span ℝ
          (Set.range (InnerProductSpace.gramSchmidt ℝ v)) :=
      InnerProductSpace.span_gramSchmidtNormed_range v
    _ = Submodule.span ℝ (Set.range v) :=
      InnerProductSpace.span_gramSchmidt ℝ v

/-- 一组基经 Gram–Schmidt 后仍是基，并且成为标准正交基。
@isnad1 id=and.1h3v.s6.9bb5db3b84b7 from=translated src=- shape=c255e890 vocab=26f35fed
-/
theorem orthonormalize_basis {n : ℕ} {b : Fin n → E}
    (hb : IsBasis ℝ b) :
    IsBasis ℝ (orthonormalize b) ∧ Orthonormal ℝ (orthonormalize b) := by
  refine ⟨⟨orthonormalize_is_linearly_independent hb.1, ?_⟩,
    orthonormalize_is_orthonormal hb.1⟩
  rw [orthonormalize_span_eq]
  exact hb.2

/-! ## 正交投影与正交分解 -/

/-- `x` 是有限向量组 `v` 的线性组合。这个教材谓词把底层“张成子空间”藏在
公开接口之后。-/
def IsLinearCombination {n : ℕ} (v : Fin n → E) (x : E) : Prop :=
  ∃ c : Fin n → ℝ, ∑ i, c i • v i = x

/-- `x` 与向量组 `v` 中的每个向量都正交。-/
def IsOrthogonalToFamily {n : ℕ} (x : E) (v : Fin n → E) : Prop :=
  ∀ i, AreOrthogonal x (v i)

/-- 有限维实内积空间中的正交分解：任意向量都能唯一地写成给定有限向量组的
线性组合与一个垂直于该向量组的向量之和。
@isnad1 id=existsun.0h4v.s6.a766b9f2b98b from=translated src=- shape=76fd3a45 vocab=7aa0e220
-/
theorem orthogonal_decomposition {n : ℕ} [FiniteDimensional ℝ E]
    (v : Fin n → E) (x : E) :
    ∃! yz : E × E,
      IsLinearCombination v yz.1 ∧
        IsOrthogonalToFamily yz.2 v ∧ x = yz.1 + yz.2 := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  let y : E := K.starProjection x
  let z : E := x - y
  have hyK : y ∈ K := K.starProjection_apply_mem x
  have hy : IsLinearCombination v y := by
    rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hyK with ⟨c, hc⟩
    exact ⟨c, hc⟩
  have hz : IsOrthogonalToFamily z v := by
    intro i
    exact K.starProjection_inner_eq_zero x (v i)
      (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨(y, z), ⟨hy, hz, by simp [z]⟩, ?_⟩
  intro yz hyz
  rcases yz with ⟨y', z'⟩
  rcases hyz with ⟨hy', hz', hsum⟩
  have hy'K : y' ∈ K := by
    rcases hy' with ⟨c, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩
  have horth : ∀ w ∈ K, inner ℝ (x - y') w = 0 := by
    intro w hw
    rw [hsum, add_sub_cancel_left]
    rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw with ⟨d, rfl⟩
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hzi := hz' i
    change inner ℝ z' (v i) = 0 at hzi
    simp [inner_smul_right, hzi]
  have hproj : y = y' := by
    exact K.eq_starProjection_of_mem_of_inner_eq_zero hy'K horth
  apply Prod.ext
  · exact hproj.symm
  · calc
      z' = x - y' := by rw [hsum]; abel
      _ = x - y := by rw [hproj]
      _ = z := rfl

/-! ## 伴随与自伴算子 -/

/-- 有限维实内积空间上线性算子的伴随。-/
noncomputable def adjointOperator [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  T.adjoint

/-- 伴随算子的刻画公式：`⟪x,T*y⟫ = ⟪Tx,y⟫`。
@isnad1 id=eq.0h4v.s8.eeecd78ff88c from=translated src=- shape=0ab6017b vocab=25581b6d
-/
theorem adjoint_characterization [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (x y : E) :
    inner ℝ x (adjointOperator T y) = inner ℝ (T x) y :=
  T.adjoint_inner_right x y

/-- 自伴算子的教材定义。-/
def IsSelfAdjointOperator (T : E →ₗ[ℝ] E) : Prop :=
  ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)

/-- 在有限维实内积空间中，一个算子自伴当且仅当它等于自己的伴随。
@isnad1 id=iff.0h2v.s7.8261879c6ae4 from=translated src=- shape=7f4a1945 vocab=55cdbb99
-/
theorem self_adjoint_iff_eq_adjoint [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) :
    IsSelfAdjointOperator T ↔ adjointOperator T = T := by
  change T.IsSymmetric ↔ T.adjoint = T
  exact ⟨LinearMap.IsSymmetric.adjoint_eq,
    fun h => (LinearMap.eq_adjoint_iff T T).mp h.symm⟩

end SandronesLibrary.LinearAlgebra.InnerProduct
