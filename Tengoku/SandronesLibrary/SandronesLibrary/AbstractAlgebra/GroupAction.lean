/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.GroupProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 群作用、轨道与稳定子

群作用把群元素解释为集合上的对称变换：`g • x` 表示以 `g` 变换点 `x`。作用必须满足
单位元不移动点以及群乘法对应连续执行两次变换。本文件由此建立轨道、稳定子、传递作用、
轨道—稳定子定理，并把共轭作用的轨道分解专门化为有限群的类方程。
-/

namespace SandronesLibrary
namespace AbstractAlgebra.Group

/-- 群作用的单位元公理：单位元固定每个点。
> **Entry**: abstract-algebra.group.action
@isnad1 id=eq.0h3v.s5.ffccb3db2739 from=translated src=- shape=74abeac4 vocab=026f8054
-/
theorem action_one {G X : Type*} [Group G] [MulAction G X] (x : X) :
    (1 : G) • x = x := by
  exact one_smul G x

/-- 群作用的乘法相容公理：`gh` 的作用等于先作用 `h`、再作用 `g`。
> **Entry**: abstract-algebra.group.action
@isnad1 id=eq.0h5v.s6.c9e3a5f26907 from=translated src=- shape=a1381cd9 vocab=992284b8
-/
theorem action_mul {G X : Type*} [Group G] [MulAction G X]
    (g h : G) (x : X) : (g * h) • x = g • h • x := by
  exact mul_smul g h x

/-- 点 `x` 的轨道由所有 `g • x` 组成。
> **Entry**: abstract-algebra.group.action
@isnad1 id=iff.0h4v.s6.8b0a6464d3a8 from=translated src=- shape=91bbd704 vocab=0b23e9cd
-/
theorem orbit_mem_iff {G X : Type*} [Group G] [MulAction G X] (x y : X) :
    y ∈ MulAction.orbit G x ↔ ∃ g : G, g • x = y := by
  exact MulAction.mem_orbit_iff

/-- 点 `x` 的稳定子由所有固定 `x` 的群元素组成。
> **Entry**: abstract-algebra.group.action
@isnad1 id=iff.0h4v.s6.0bcf3858fa0c from=translated src=- shape=278f4716 vocab=fc7d4361
-/
theorem stabilizer_mem_iff {G X : Type*} [Group G] [MulAction G X]
    (x : X) (g : G) :
    g ∈ MulAction.stabilizer G x ↔ g • x = x := by
  exact MulAction.mem_stabilizer_iff

/-- 两个轨道相等当且仅当其中一个代表元落在另一个轨道中。由此可见不同轨道不交，
所以轨道构成作用集合的分割。
> **Entry**: abstract-algebra.group.action
@isnad1 id=iff.0h4v.s6.4ba83c9d4bda from=translated src=- shape=5ab63917 vocab=8cb18eb1
-/
theorem orbit_eq_iff_mem {G X : Type*} [Group G] [MulAction G X] (x y : X) :
    MulAction.orbit G x = MulAction.orbit G y ↔ x ∈ MulAction.orbit G y := by
  exact MulAction.orbit_eq_iff

/-- **轨道—稳定子定理的结构形式**：点 `x` 的轨道与稳定子的左陪集空间
`G / Gₓ` 等价。这里稳定子一般不正规，所以结论是集合等价而不是群同构。
> **Entry**: abstract-algebra.group.action-/
noncomputable def orbitEquivCosets {G X : Type*} [Group G] [MulAction G X] (x : X) :
    MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

/-- 同一轨道中两点的稳定子彼此群同构；更精确地说，它们在 `G` 中互为共轭子群。
> **Entry**: abstract-algebra.group.action-/
noncomputable def stabilizerEquivOfSameOrbit {G X : Type*} [Group G] [MulAction G X]
    {x y : X} (h : MulAction.orbitRel G X x y) :
    MulAction.stabilizer G x ≃* MulAction.stabilizer G y :=
  MulAction.stabilizerEquivStabilizerOfOrbitRel h

/-- **轨道—稳定子公式**：`|Orb(x)| · |Gₓ| = |G|`。

使用 `Nat.card` 可统一陈述有限与无限类型；在通常有限群情形中，这就是教材中的群阶公式。
> **Entry**: abstract-algebra.group.action
@isnad1 id=eq.0h3v.s6.d80a54bc6bc5 from=translated src=- shape=d2b3f447 vocab=ce58e633
-/
theorem orbit_stabilizer_card {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) *
      Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

/-- 作用是传递的，当且仅当任取一个点，其轨道都是整个作用集合。
> **Entry**: abstract-algebra.group.action
@isnad1 id=iff.0h3v.s6.1dd090ef9446 from=translated src=- shape=8b9349ac vocab=207b6263
-/
theorem pretransitive_iff_orbit_eq_univ {G X : Type*} [Group G] [MulAction G X]
    (x : X) :
    MulAction.IsPretransitive G X ↔ MulAction.orbit G x = Set.univ := by
  exact MulAction.isPretransitive_iff_orbit_eq_univ (G := G) x

/-- **有限群的类方程**：群阶等于中心阶加上所有非中心共轭类的大小之和。

这是把轨道分割用于 `G` 对自身的共轭作用所得的公式；中心元素对应恰含一个元素的轨道。
> **Entry**: abstract-algebra.group.action
@isnad1 id=eq.0h1v.s7.21085117d27b from=translated src=- shape=c601534d vocab=ed59653d
-/
theorem finite_group_class_equation (G : Type*) [Group G] [Finite G] :
    Nat.card (Subgroup.center G) +
      ∑ᶠ C ∈ ConjClasses.noncenter G, Nat.card C.carrier = Nat.card G := by
  exact Group.nat_card_center_add_sum_card_noncenter_eq_card G

end AbstractAlgebra.Group
end SandronesLibrary
