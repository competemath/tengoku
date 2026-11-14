/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AbstractAlgebra / GroupCyclic —— 循环群与元素阶

本文件发展群论课程中的循环群基础。元素 `g` 生成的循环子群由其所有整数次幂组成；
群是循环群，当且仅当某个元素生成全群。有限情形下，生成元的阶等于群的阶。

进一步证明循环群的每个子群仍是循环群，并给出位于 `⟨g⟩` 中的子群形如 `⟨gⁿ⟩`
的分类接口。最后得到经典结论：素数阶群中任意非单位元都是生成元。

> **Entry**: abstract-algebra.group.cyclic
-/

namespace SandronesLibrary.AbstractAlgebra.Group

/-- 元素 `g` 生成的循环子群 `⟨g⟩`，即 `g` 的所有整数次幂组成的子群。-/
def cyclicSubgroup {G : Type*} [Group G] (g : G) : Subgroup G :=
  Subgroup.zpowers g

/-- `x ∈ ⟨g⟩` 当且仅当存在整数 `n` 使 `gⁿ = x`。这正是循环子群的元素刻画。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=iff.0h3v.s5.64ca56f2ef41 from=translated src=- shape=43237c85 vocab=c11774cf
-/
theorem mem_cyclicSubgroup_iff {G : Type*} [Group G] (g x : G) :
    x ∈ cyclicSubgroup g ↔ ∃ n : ℤ, g ^ n = x := by
  exact Subgroup.mem_zpowers_iff

/-- 循环子群 `⟨g⟩` 的基数等于元素 `g` 的阶。无限阶时两边按 `Nat.card` 约定均为零。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=eq.0h2v.s5.331fa8e62428 from=translated src=- shape=2724daa3 vocab=14fb1f84
-/
theorem cyclicSubgroup_card {G : Type*} [Group G] (g : G) :
    Nat.card (cyclicSubgroup g) = orderOf g := by
  exact Nat.card_zpowers g

/-- **循环群的生成元判据**：`G` 是循环群，当且仅当存在 `g` 使 `⟨g⟩ = G`。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=iff.0h1v.s5.c929380f49b1 from=translated src=- shape=59ecdcff vocab=e13c4ef7
-/
theorem cyclic_iff_exists_generator {G : Type*} [Group G] :
    IsCyclic G ↔ ∃ g : G, cyclicSubgroup g = ⊤ := by
  exact isCyclic_iff_exists_zpowers_eq_top

/-- 若 `g` 生成整个群，则 `g` 的阶等于群的阶。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=eq.1h2v.s5.cdb2df0df760 from=translated src=- shape=78fd5d17 vocab=3e0caeb0
-/
theorem generator_order_eq_group_card {G : Type*} [Group G] {g : G}
    (hg : cyclicSubgroup g = ⊤) :
    orderOf g = Nat.card G := by
  exact orderOf_eq_card_of_zpowers_eq_top hg

/-- **循环群的子群仍是循环群**。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=iscyclic.0h2v.s5.10c305d024ed from=translated src=- shape=2737fe64 vocab=3d66f7e8
-/
theorem subgroup_of_cyclic_is_cyclic {G : Type*} [Group G] [IsCyclic G]
    (H : Subgroup G) : IsCyclic H := by
  infer_instance

/-- **循环群子群的形状**：若 `H ≤ ⟨g⟩`，则存在自然数 `n` 使 `H = ⟨gⁿ⟩`。
这给出了循环群子群分类的核心存在性陈述。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=ex.1h3v.s5.5627d7bed255 from=translated src=- shape=a39fe70c vocab=92ae8c08
-/
theorem subgroup_of_cyclic_eq_cyclicSubgroup {G : Type*} [Group G]
    (g : G) (H : Subgroup G) (hH : H ≤ cyclicSubgroup g) :
    ∃ n : ℕ, H = cyclicSubgroup (g ^ n) := by
  exact (Subgroup.le_zpowers_iff g H).1 hH

/-- **素数阶群是循环群**：更强地，任意非单位元都生成全群。
这是 Lagrange 定理与“素数只有平凡因子”的直接结合。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=eq.2h3v.s5.ab82b73f6850 from=translated src=- shape=c58847b7 vocab=0676059f
-/
theorem prime_card_group_generated_by_nonidentity {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card G = p)
    {g : G} (hg : g ≠ 1) : cyclicSubgroup g = ⊤ := by
  exact zpowers_eq_top_of_prime_card hcard hg

/-! ### 有限循环群与 Z/nZ -/

/-- 给定阶为 n 的循环群 G 及指定生成元 g，构造
`Multiplicative (ZMod n) ≃* G`。这个同构把剩余类的加法解释为 g 的指数相加。
> **Entry**: abstract-algebra.group.cyclic-/
noncomputable def zmodEquivOfGenerator {G : Type*} [Group G]
    {g : G} {n : ℕ} (hg : cyclicSubgroup g = ⊤) (hn : Nat.card G = n) :
    Multiplicative (ZMod n) ≃* G :=
  zmodMulEquivOfGenerator (fun x => hg.ge (Subgroup.mem_top x)) hn

/-- 上述同构把整数 k 的剩余类送到 `g^k`。这既说明映射的计算规则，也说明指数
相差 n 的整数给出同一个群元素。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=eq.2h4v.s7.e016351d9af7 from=translated src=- shape=42642b5a vocab=8a001a62
-/
theorem zmodEquivOfGenerator_apply_intCast {G : Type*} [Group G]
    {g : G} {n : ℕ} (hg : cyclicSubgroup g = ⊤) (hn : Nat.card G = n)
    (k : ℤ) :
    zmodEquivOfGenerator hg hn (Multiplicative.ofAdd (k : ZMod n)) = g ^ k := by
  exact zmodMulEquivOfGenerator_apply_ofAdd_intCast
    (fun x => hg.ge (Subgroup.mem_top x)) hn k

/-- 特别地，`1 mod n` 在指定生成元同构下映到 g。
> **Entry**: abstract-algebra.group.cyclic
@isnad1 id=eq.2h3v.s7.2168834bd039 from=translated src=- shape=ac8ac7bf vocab=fd284baf
-/
theorem zmodEquivOfGenerator_apply_one {G : Type*} [Group G]
    {g : G} {n : ℕ} (hg : cyclicSubgroup g = ⊤) (hn : Nat.card G = n) :
    zmodEquivOfGenerator hg hn (Multiplicative.ofAdd 1) = g := by
  exact zmodMulEquivOfGenerator_apply_ofAdd_one
    (fun x => hg.ge (Subgroup.mem_top x)) hn

/-- **循环群分类**：任意循环群 G 与其 `Nat.card` 对应的
`Multiplicative (ZMod |G|)` 同构。有限群得到通常的 `Z/nZ`；无限循环群的
`Nat.card` 为零，而 `ZMod 0` 正是整数加法群，因此同一陈述也覆盖无限情形。
> **Entry**: abstract-algebra.group.cyclic-/
noncomputable def cyclicGroupEquivZMod {G : Type*} [Group G] (hG : IsCyclic G) :
    G ≃* Multiplicative (ZMod (Nat.card G)) :=
  (zmodCyclicMulEquiv hG).symm

/-- 两个同阶循环群同构。因此有限循环群在同构意义下完全由群阶决定。
> **Entry**: abstract-algebra.group.cyclic-/
noncomputable def cyclicGroupsEquivOfCardEq
    {G H : Type*} [Group G] [Group H] [IsCyclic G] [IsCyclic H]
    (hcard : Nat.card G = Nat.card H) : G ≃* H :=
  mulEquivOfCyclicCardEq hcard

/-- 两个阶都等于同一素数 p 的群同构；它们都由任一非单位元生成。
> **Entry**: abstract-algebra.group.cyclic-/
noncomputable def primeCardGroupsEquiv {G H : Type*} [Group G] [Group H]
    {p : ℕ} [Fact p.Prime] (hG : Nat.card G = p) (hH : Nat.card H = p) :
    G ≃* H :=
  mulEquivOfPrimeCardEq hG hH

end SandronesLibrary.AbstractAlgebra.Group
