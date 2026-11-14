/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.GroupPermutation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `p`-群、Cauchy 定理与 Sylow 三定理

本文件先用教材语言定义 `p`-群和 Sylow `p`-子群，再陈述 Sylow 三定理。固定素数 `p`：
若群中每个元素都被某个 `p` 的幂次消去，就称它为 `p`-群；若一个 `p`-子群在所有
`p`-子群中关于包含关系极大，就称它为 Sylow `p`-子群。

因此公开接口只谈普通子群和上述两个本库概念。Mathlib 的 `IsPGroup` 与 `Sylow` 仅在
证明内部充当经过验证的实现桥，不再承担本文件的教材定义。
-/

open scoped Pointwise

namespace SandronesLibrary
namespace AbstractAlgebra.Group

/-- **`p`-群**：群 `G` 的每个元素 `g` 都满足 `g ^ (p ^ k) = 1`，其中指数 `k`
可以依赖于 `g`。当 `p` 为素数时，这等价于每个元素的阶都是 `p` 的幂。
> **Entry**: abstract-algebra.group.sylow-/
def IsPrimePowerGroup (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1

/-- 本库 `p`-群定义与底层实现之间的桥。它是定义展开后的同一命题，而非额外数学假设。
> **Entry**: abstract-algebra.group.sylow-/
theorem isPrimePowerGroup_iff_mathlib {p : ℕ} {G : Type*} [Group G] :
    IsPrimePowerGroup p G ↔ IsPGroup p G := by
  rfl

/-- **Sylow `p`-子群**：`P` 本身是 `p`-群，并且不存在真包含它的更大 `p`-子群。
这里“极大”是按子群包含关系而言，不是说 `P` 在所有真子群中极大。
> **Entry**: abstract-algebra.group.sylow-/
def IsSylowSubgroup {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) : Prop :=
  IsPrimePowerGroup p P ∧
    ∀ ⦃Q : Subgroup G⦄, IsPrimePowerGroup p Q → P ≤ Q → Q = P

/-- 群 `G` 的所有 Sylow `p`-子群组成的类型。其元素包含一个普通子群以及该子群具有
Sylow 性质的证明；`Nat.card (SylowSubgroup p G)` 就是教材中的 `nₚ`。
> **Entry**: abstract-algebra.group.sylow-/
def SylowSubgroup (p : ℕ) (G : Type*) [Group G] :=
  {P : Subgroup G // IsSylowSubgroup p P}

namespace IsSylowSubgroup

/-- Sylow `p`-子群首先是一个 `p`-子群。-/
theorem isPGroup {G : Type*} [Group G] {p : ℕ} {P : Subgroup G}
    (hP : IsSylowSubgroup p P) : IsPrimePowerGroup p P := hP.1

/-- Sylow `p`-子群在 `p`-子群中关于包含关系极大。-/
theorem maximal {G : Type*} [Group G] {p : ℕ} {P Q : Subgroup G}
    (hP : IsSylowSubgroup p P) (hQ : IsPrimePowerGroup p Q) (hPQ : P ≤ Q) : Q = P :=
  hP.2 hQ hPQ

end IsSylowSubgroup

/-! 以下三个私有定义只负责把本库教材表示送入 Mathlib 已验证的 Sylow 实现。 -/

private def toMathlibSylow {G : Type*} [Group G] {p : ℕ}
    (P : SylowSubgroup p G) : Sylow p G :=
  ⟨P.1, isPrimePowerGroup_iff_mathlib.mp P.2.1,
    fun hQ hPQ => P.2.2 (isPrimePowerGroup_iff_mathlib.mpr hQ) hPQ⟩

private def fromMathlibSylow {G : Type*} [Group G] {p : ℕ}
    (P : Sylow p G) : SylowSubgroup p G :=
  ⟨P, isPrimePowerGroup_iff_mathlib.mpr P.isPGroup',
    fun {_Q} hQ hPQ => P.is_maximal' (isPrimePowerGroup_iff_mathlib.mp hQ) hPQ⟩

private def sylowEquivMathlib (p : ℕ) (G : Type*) [Group G] :
    SylowSubgroup p G ≃ Sylow p G where
  toFun := toMathlibSylow
  invFun := fromMathlibSylow
  left_inv P := by
    apply Subtype.ext
    simp [fromMathlibSylow, toMathlibSylow]
  right_inv P := by
    apply Sylow.ext
    simp [fromMathlibSylow, toMathlibSylow]

/-- **Cauchy 定理**：若素数 `p` 整除有限群 `G` 的阶，则 `G` 中存在阶为 `p` 的元素。
> **Entry**: abstract-algebra.group.sylow-/
theorem cauchy_theorem {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card G) :
    ∃ g : G, orderOf g = p := by
  exact exists_prime_orderOf_dvd_card' p hp

/-- **Sylow 第一定理（存在性）**：每个群都存在 Sylow `p`-子群。
在有限群且 `p` 为素数时，后面的 `sylow_card` 给出它的精确阶。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_exists (G : Type*) [Group G] (p : ℕ) :
    Nonempty (SylowSubgroup p G) := by
  exact Nonempty.map (sylowEquivMathlib p G).symm Sylow.nonempty

/-- Sylow 第一定理的包含形式：每个 `p`-子群都包含于某个 Sylow `p`-子群。
> **Entry**: abstract-algebra.group.sylow-/
theorem pSubgroup_le_sylow {G : Type*} [Group G] {p : ℕ}
    {H : Subgroup G} (hH : IsPrimePowerGroup p H) :
    ∃ P : SylowSubgroup p G, H ≤ P.1 := by
  obtain ⟨P, hHP⟩ := (isPrimePowerGroup_iff_mathlib.mp hH).exists_le_sylow
  exact ⟨fromMathlibSylow P, hHP⟩

/-- 有限群的 Sylow `p`-子群阶为 `p ^ v_p(|G|)`，即群阶中最大的 `p` 次幂因子。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : SylowSubgroup p G) :
    Nat.card P.1 = p ^ (Nat.card G).factorization p := by
  exact (toMathlibSylow P).card_eq_multiplicity

/-- **Sylow 第二定理**：任意两个 Sylow `p`-子群在 `G` 中互为共轭。这里共轭子群
写作自同构 `x ↦ g x g⁻¹` 对子群的像。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_conjugate {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] [Finite (SylowSubgroup p G)] (P Q : SylowSubgroup p G) :
    ∃ g : G, P.1.map (MulAut.conj g).toMonoidHom = Q.1 := by
  let _ : Finite (Sylow p G) := (sylowEquivMathlib p G).finite_iff.mp inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (toMathlibSylow P) (toMathlibSylow Q)
  refine ⟨g, ?_⟩
  have hsub := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul] at hsub
  change MulAut.conj g • P.1 = Q.1
  simpa [toMathlibSylow] using hsub

/-- **Sylow 第三定理（同余条件）**：Sylow `p`-子群个数 `nₚ` 模 `p` 余一。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_number_mod_prime {G : Type*} [Group G] (p : ℕ)
    [Fact p.Prime] [Finite (SylowSubgroup p G)] :
    Nat.card (SylowSubgroup p G) ≡ 1 [MOD p] := by
  let _ : Finite (Sylow p G) := (sylowEquivMathlib p G).finite_iff.mp inferInstance
  rw [Nat.card_congr (sylowEquivMathlib p G)]
  exact card_sylow_modEq_one p G

/-- **Sylow 第三定理（整除条件）**：`nₚ` 整除任一 Sylow `p`-子群在 `G` 中的指数。
在有限群中，该指数是 `|G| / |P|`。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_number_dvd_index {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] [Finite (SylowSubgroup p G)] (P : SylowSubgroup p G) :
    Nat.card (SylowSubgroup p G) ∣ P.1.index := by
  let _ : Finite (Sylow p G) := (sylowEquivMathlib p G).finite_iff.mp inferInstance
  rw [Nat.card_congr (sylowEquivMathlib p G)]
  exact (toMathlibSylow P).card_dvd_index

/-- 若 Sylow `p`-子群唯一，则它正规：任意共轭仍是 Sylow 子群，唯一性迫使共轭固定它。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_normal_of_unique {G : Type*} [Group G] {p : ℕ}
    (P : SylowSubgroup p G) (hP : ∀ Q : SylowSubgroup p G, Q = P) : P.1.Normal := by
  let _ : Subsingleton (SylowSubgroup p G) := ⟨fun Q R => (hP Q).trans (hP R).symm⟩
  let _ : Subsingleton (Sylow p G) := Equiv.subsingleton (sylowEquivMathlib p G).symm
  exact (toMathlibSylow P).normal_of_subsingleton

/-- 反之，正规的 Sylow `p`-子群唯一。结合上一条可得教材判据：Sylow `p`-子群正规
当且仅当 `nₚ = 1`。
> **Entry**: abstract-algebra.group.sylow-/
theorem sylow_unique_of_normal {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] [Finite (SylowSubgroup p G)] (P : SylowSubgroup p G) (hP : P.1.Normal) :
    ∀ Q : SylowSubgroup p G, Q = P := by
  let _ : Finite (Sylow p G) := (sylowEquivMathlib p G).finite_iff.mp inferInstance
  let _ := (toMathlibSylow P).unique_of_normal hP
  intro Q
  apply (sylowEquivMathlib p G).injective
  exact Subsingleton.elim _ _

/-- **低阶群应用**：素数平方阶群必为交换群。

证明利用 `p`-群作用的中心非平凡性：中心阶只能为 `p` 或 `p²`；前者使中心商为
素数阶循环群，后者使中心等于全群，两种情形都推出交换性。
> **Entry**: abstract-algebra.group.sylow-/
theorem prime_square_group_commutative {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : Nat.card G = p ^ 2) :
    IsMulCommutative G := by
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hG

end AbstractAlgebra.Group
end SandronesLibrary
