/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.GroupAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 置换群、循环分解与交错群

集合 `X` 上的置换是 `X` 到自身的双射；置换以复合为乘法，组成对称群 `Sym(X)`。
本文件先用 Cayley 定理说明每个群都可实现为某个对称群的子群，再处理有限置换的
互不相交循环分解和换位分解。符号同态把置换分成偶置换与奇置换，其核即交错群。
-/

namespace SandronesLibrary
namespace AbstractAlgebra.Group

/-- 集合 `X` 上的对称群；其元素是 `X` 的全部置换。
> **Entry**: abstract-algebra.group.permutation-/
abbrev SymmetricGroup (X : Type*) := Equiv.Perm X

/-- 置换的支集由它实际移动的点组成。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=iff.0h3v.s5.25171c683552 from=translated src=- shape=4bb9d6fa vocab=9db75d91
-/
theorem permutation_mem_support_iff {X : Type*} [Fintype X] [DecidableEq X]
    (σ : SymmetricGroup X) (x : X) : x ∈ σ.support ↔ σ x ≠ x := by
  exact Equiv.Perm.mem_support

/-- **Cayley 定理**：每个群 `G` 都同构于其正则作用在 `G` 上所诱导的置换群子群。
因此抽象群均可具体实现为对称群的子群。
> **Entry**: abstract-algebra.group.permutation-/
noncomputable def cayleyEquiv {G : Type*} [Group G] :
    G ≃* (MulAction.toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

/-- 规范循环分解中的每个因子确实是一个非平凡循环。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=iscycle.1h3v.s5.3c6b52450d2a from=translated src=- shape=c043df82 vocab=66c4738d
-/
theorem cycleFactor_isCycle {X : Type*} [Fintype X] [DecidableEq X]
    (σ c : SymmetricGroup X) (hc : c ∈ σ.cycleFactorsFinset) : c.IsCycle := by
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1

/-- 规范循环分解的不同循环支集两两不交。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=pairwise.0h2v.s4.95d0a9984924 from=translated src=- shape=27030dc7 vocab=d03344c3
-/
theorem cycleFactors_pairwise_disjoint {X : Type*} [Fintype X] [DecidableEq X]
    (σ : SymmetricGroup X) :
    (σ.cycleFactorsFinset : Set (SymmetricGroup X)).Pairwise Equiv.Perm.Disjoint := by
  exact σ.cycleFactorsFinset_pairwise_disjoint

/-- **互不相交循环分解**：规范循环因子的乘积等于原置换。
因子两两不交，故彼此交换，有限集乘积不依赖枚举次序。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=eq.0h2v.s5.d9c0648fd9ea from=translated src=- shape=31e172fe vocab=01c61518
-/
theorem permutation_eq_product_cycleFactors {X : Type*} [Fintype X] [DecidableEq X]
    (σ : SymmetricGroup X) :
    σ.cycleFactorsFinset.noncommProd id σ.cycleFactorsFinset_mem_commute = σ := by
  exact σ.cycleFactorsFinset_noncommProd

/-- 每个有限置换都能写成有限个换位的乘积。这样的表示通常不唯一。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=ex.0h2v.s5.f8738371c7ff from=translated src=- shape=dc85a8b4 vocab=db98ac16
-/
theorem exists_transposition_factorization {X : Type*}
    [Finite X] [DecidableEq X] (σ : SymmetricGroup X) :
    ∃ l : List (SymmetricGroup X),
      l.prod = σ ∧ ∀ τ ∈ l, Equiv.Perm.IsSwap τ := by
  classical
  cases nonempty_fintype X
  exact ⟨(Equiv.Perm.truncSwapFactors σ).out.1,
    (Equiv.Perm.truncSwapFactors σ).out.2⟩

/-- 置换的符号同态 `sgn : Sym(X) → {±1}`；值 `1` 表示偶置换，`-1` 表示奇置换。
> **Entry**: abstract-algebra.group.permutation-/
def permutationSign {X : Type*} [Fintype X] [DecidableEq X] :
    SymmetricGroup X →* ℤˣ := Equiv.Perm.sign

/-- 符号保持置换乘法。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=eq.0h3v.s7.96a4fa2228d0 from=translated src=- shape=678d1021 vocab=66f69a1d
-/
theorem permutationSign_mul {X : Type*} [Fintype X] [DecidableEq X]
    (σ τ : SymmetricGroup X) :
    permutationSign (σ * τ) = permutationSign σ * permutationSign τ := by
  exact Equiv.Perm.sign_mul σ τ

/-- 任意非平凡换位都是奇置换。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=eq.1h3v.s6.7ed10cf1dea2 from=translated src=- shape=e988fdca vocab=a784bf68
-/
theorem transposition_is_odd {X : Type*} [Fintype X] [DecidableEq X]
    {x y : X} (hxy : x ≠ y) : permutationSign (Equiv.swap x y) = -1 := by
  exact Equiv.Perm.sign_swap hxy

/-- 交错群 `Alt(X)` 恰由所有偶置换组成，即符号同态的核。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=iff.0h2v.s6.ff3ddfbaaa2d from=translated src=- shape=cb1e1695 vocab=879f9f1f
-/
theorem alternatingGroup_mem_iff_even {X : Type*} [Fintype X] [DecidableEq X]
    (σ : SymmetricGroup X) :
    σ ∈ alternatingGroup X ↔ permutationSign σ = 1 := by
  exact Equiv.Perm.mem_alternatingGroup

/-- 一组换位的乘积是偶置换，当且仅当换位个数为偶数。这说明虽然换位分解不唯一，
但分解长度的奇偶性只由最终置换决定。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=iff.1h2v.s6.ed984b0ed8d2 from=translated src=- shape=bb4c4a7d vocab=3b072819
-/
theorem transposition_factorization_even_iff {X : Type*}
    [Fintype X] [DecidableEq X] (l : List (SymmetricGroup X))
    (hl : ∀ τ ∈ l, Equiv.Perm.IsSwap τ) :
    l.prod ∈ alternatingGroup X ↔ Even l.length := by
  exact Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length hl

/-- 当 `X` 至少有两个元素时，交错群在对称群中的指数为 `2`。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=eq.0h1v.s4.b546eb0df777 from=translated src=- shape=792da867 vocab=ec2fa990
-/
theorem alternatingGroup_index_two {X : Type*} [Fintype X] [DecidableEq X]
    [Nontrivial X] : (alternatingGroup X).index = 2 := by
  exact alternatingGroup.index_eq_two

/-- 有限集合 `X` 至少含两个元素时，交错群的阶为 `|X|!/2`。
> **Entry**: abstract-algebra.group.permutation
@isnad1 id=eq.0h1v.s6.4047f1eb592e from=translated src=- shape=c03a2a4b vocab=1ee7991a
-/
theorem alternatingGroup_card {X : Type*} [Fintype X] [DecidableEq X]
    [Nontrivial X] :
    Fintype.card (alternatingGroup X) = (Fintype.card X).factorial / 2 := by
  exact card_alternatingGroup

end AbstractAlgebra.Group
end SandronesLibrary
