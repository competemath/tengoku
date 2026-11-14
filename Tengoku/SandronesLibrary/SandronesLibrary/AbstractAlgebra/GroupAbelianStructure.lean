/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.GroupSylow
import Tengoku.Seed.GroupTheory.FiniteAbelian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 有限生成交换群结构定理

有限生成交换群由两类不可约的基本成分组成：无限循环群 `ℤ` 给出自由部分，素数幂阶
循环群给出有限挠部分。有限群没有自由部分，所以完全分解为有限个有限循环群的直积。

本文件首先以“存在有限生成集”定义有限生成群，再给出一般有限生成交换群的结构定理、
有限交换群的初等因子形式，以及“有限当且仅当同构于有限个非平凡有限循环群之直积”的
双向分类陈述。
-/

open scoped DirectSum

namespace SandronesLibrary
namespace AbstractAlgebra.Group

/-- **有限生成群**：存在有限集合 `S`，由 `S` 生成的子群就是整个群。

这个定义只使用本库已有的 `generatedSubgroup`，是教材中“`G = ⟨S⟩` 且 `S` 有限”的
直接翻译。
> **Entry**: abstract-algebra.group.abelian-structure-/
def IsFinitelyGeneratedGroup (G : Type*) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ generatedSubgroup S = ⊤

/-- 本库有限生成定义与底层 `Group.FG` 实现等价。底层结构只用于调用已经验证的分类
算法；后续公开主定理仍以 `IsFinitelyGeneratedGroup` 为前提。
> **Entry**: abstract-algebra.group.abelian-structure
@isnad1 id=iff.0h1v.s3.da754497ff88 from=translated src=- shape=aa7e0af4 vocab=bbe5ff79
-/
theorem isFinitelyGeneratedGroup_iff_mathlib {G : Type*} [Group G] :
    IsFinitelyGeneratedGroup G ↔ Group.FG G := by
  rw [Group.fg_iff]
  simp only [IsFinitelyGeneratedGroup, generatedSubgroup]
  exact exists_congr fun S => and_comm

/-- 每个有限群都是有限生成群：可直接取全体群元素作为有限生成集。
> **Entry**: abstract-algebra.group.abelian-structure
@isnad1 id=isfinite.0h1v.s3.ae86df290dd9 from=translated src=- shape=c612a321 vocab=4647869d
-/
theorem finite_group_isFinitelyGenerated (G : Type*) [Group G] [Finite G] :
    IsFinitelyGeneratedGroup G := by
  exact isFinitelyGeneratedGroup_iff_mathlib.mpr inferInstance

/-- **有限生成交换群结构定理（初等因子形式）**：存在自然数 `r` 和有限指标集 `ι`，
使 `G` 同构于 `r` 个无限循环群与有限多个素数幂阶循环群的直积：

`G ≅ ℤ^r × ∏ i, ℤ/(pᵢ ^ eᵢ)ℤ`。

`r` 是自由秩；每个 `p i` 都是素数。指数为零的因子是平凡群，不影响同构类型。
> **Entry**: abstract-algebra.group.abelian-structure
@isnad1 id=ex.1h1v.s8.b6421c3b841f from=translated src=- shape=ea8a0b42 vocab=3a30a9b8
-/
theorem finitely_generated_abelian_structure (G : Type*) [CommGroup G]
    (hG : IsFinitelyGeneratedGroup G) :
    ∃ (r : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty (G ≃* (Fin r → Multiplicative ℤ) ×
        ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) := by
  let _ : Group.FG G := isFinitelyGeneratedGroup_iff_mathlib.mp hG
  obtain ⟨ι, j, hι, hj, p, hp, e, h⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  let r := Fintype.card j
  let jr : j ≃ Fin r := Fintype.equivFin j
  refine ⟨r, ι, hι, p, hp, e, ?_⟩
  exact Nonempty.map (fun equiv => equiv.trans
    ((MulEquiv.arrowCongr jr (MulEquiv.refl _)).prodCongr (MulEquiv.refl _))) h

/-- **有限交换群基本定理（初等因子形式）**：有限交换群是有限多个素数幂阶循环群
的直积。与一般结构定理相比，有限性迫使自由秩为零。
> **Entry**: abstract-algebra.group.abelian-structure
@isnad1 id=ex.0h1v.s7.c8e5a9373dbb from=translated src=- shape=b03a69e1 vocab=4959985a
-/
theorem finite_abelian_prime_power_structure (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ)
      (_ : ∀ i, Nat.Prime (p i)) (e : ι → ℕ),
      Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) := by
  obtain ⟨ι, hι, p, hp, e, ⟨equiv⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite (Additive G)
  refine ⟨ι, hι, p, hp, e, ?_⟩
  exact ⟨MulEquiv.toAdditive.symm <| equiv.trans <|
    (DirectSum.addEquivProd _).trans (MulEquiv.piMultiplicative _).toAdditiveRight⟩

/-- **有限交换群基本定理（循环因子存在形式）**：有限交换群同构于有限多个阶大于
`1` 的循环群的直积。这里删除了所有平凡因子，但不要求各阶满足整除链。
> **Entry**: abstract-algebra.group.abelian-structure
@isnad1 id=ex.0h1v.s6.ca968c331a1e from=translated src=- shape=e33d503a vocab=c297667a
-/
theorem finite_abelian_cyclic_structure (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧
      Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) := by
  exact CommGroup.equiv_prod_multiplicative_zmod_of_finite G

/-- **有限交换群的双向分类**：交换群 `G` 有限，当且仅当它同构于有限多个非平凡
有限循环群的直积。

正向是有限交换群结构定理；反向来自每个 `ZMod (n i)` 在 `n i > 1` 时有限，以及有限
指标直积保持有限性。这个双向版本明确说明右侧标准模型恰好刻画有限交换群，而不只是为
已有有限群提供一种表示。
> **Entry**: abstract-algebra.group.abelian-structure
@isnad1 id=iff.0h1v.s6.f8455f2fe7a5 from=translated src=- shape=f233a62a vocab=c297667a
-/
theorem finite_abelian_iff_cyclic_product (G : Type*) [CommGroup G] :
    Finite G ↔
      ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
        (∀ i, 1 < n i) ∧
        Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) := by
  constructor
  · intro hG
    let _ : Finite G := hG
    exact finite_abelian_cyclic_structure G
  · rintro ⟨ι, hι, n, hn, ⟨equiv⟩⟩
    let _ : ∀ i, NeZero (n i) := fun i =>
      ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt (hn i))⟩
    let _ : ∀ i, Finite (Multiplicative (ZMod (n i))) := fun _ => inferInstance
    let _ : Finite ((i : ι) → Multiplicative (ZMod (n i))) := inferInstance
    exact Finite.of_equiv _ equiv.symm.toEquiv

end AbstractAlgebra.Group
end SandronesLibrary
