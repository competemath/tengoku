/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.GroupIsomorphismTheorems

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 群的自同构与内自同构

群 `G` 的自同构是从 `G` 到自身的群同构。自同构以函数复合为乘法，恒等映射为单位元，
逆同构为逆元，因而组成自同构群 `Aut(G)`。每个 `g : G` 还通过共轭
`x ↦ gxg⁻¹` 给出一个内自同构；所有内自同构组成 `Inn(G)`。

本文件作为半直积之前的必要铺垫：半直积的作用正是一个同态 `H → Aut(N)`。
-/

namespace SandronesLibrary
namespace AbstractAlgebra.Group

/-- 群 `G` 的自同构群 `Aut(G)`；实现上使用 mathlib 的乘法自同构群 `MulAut G`。
> **Entry**: abstract-algebra.group.automorphism-/
abbrev AutomorphismGroup (G : Type*) [Group G] := MulAut G

/-- `Aut(G)` 的单位元是恒等自同构。
> **Entry**: abstract-algebra.group.automorphism-/
def identityAutomorphism {G : Type*} [Group G] : AutomorphismGroup G := 1

/-- 恒等自同构逐点固定 `G` 中的元素。
> **Entry**: abstract-algebra.group.automorphism-/
theorem identityAutomorphism_apply {G : Type*} [Group G] (x : G) :
    identityAutomorphism x = x := rfl

/-- `Aut(G)` 的乘法是函数复合：`(σ τ)(x)=σ(τ(x))`。
> **Entry**: abstract-algebra.group.automorphism-/
theorem automorphism_comp_apply {G : Type*} [Group G]
    (σ τ : AutomorphismGroup G) (x : G) : (σ * τ) x = σ (τ x) := rfl

/-- 自同构的逆元是其逆函数，故 `σ⁻¹(σ(x))=x`。
> **Entry**: abstract-algebra.group.automorphism-/
theorem automorphism_inv_apply_apply {G : Type*} [Group G]
    (σ : AutomorphismGroup G) (x : G) : σ⁻¹ (σ x) = x := by
  exact MulAut.inv_apply_self G σ x

/-- **内自同构同态**：把 `g : G` 送到共轭自同构 `x ↦ gxg⁻¹`。
共轭满足 `conj(gh)=conj(g)conj(h)`，所以这是群同态 `G → Aut(G)`。
> **Entry**: abstract-algebra.group.automorphism-/
def innerAutomorphismHom (G : Type*) [Group G] : G →* AutomorphismGroup G :=
  MulAut.conj

/-- 内自同构的逐点计算公式。
> **Entry**: abstract-algebra.group.automorphism-/
theorem innerAutomorphismHom_apply {G : Type*} [Group G] (g x : G) :
    innerAutomorphismHom G g x = g * x * g⁻¹ := rfl

/-- 内自同构群 `Inn(G)` 是共轭同态 `G → Aut(G)` 的值域，因此自然成为
`Aut(G)` 的子群。
> **Entry**: abstract-algebra.group.automorphism-/
def innerAutomorphismGroup (G : Type*) [Group G] : Subgroup (AutomorphismGroup G) :=
  (innerAutomorphismHom G).range

/-- 共轭同态的核恰为群的中心：`conj(g)` 是恒等映射，当且仅当 `g` 与所有元素交换。
> **Entry**: abstract-algebra.group.automorphism-/
theorem innerAutomorphismHom_ker {G : Type*} [Group G] :
    (innerAutomorphismHom G).ker = Subgroup.center G := by
  ext g
  simp only [innerAutomorphismHom, MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hg x
    have hx := DFunLike.congr_fun hg x
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hx
    exact hx.symm
  · intro hg
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
    exact (hg x).symm

/-- **内自同构群定理**：第一同构定理应用于共轭同态后得到
`G/Z(G) ≃ Inn(G)`。
> **Entry**: abstract-algebra.group.automorphism-/
noncomputable def centerQuotientEquivInnerAutomorphisms {G : Type*} [Group G] :
    G ⧸ Subgroup.center G ≃* innerAutomorphismGroup G :=
  (QuotientGroup.quotientMulEquivOfEq innerAutomorphismHom_ker.symm).trans
    (firstIsomorphism (innerAutomorphismHom G))

end AbstractAlgebra.Group
end SandronesLibrary
