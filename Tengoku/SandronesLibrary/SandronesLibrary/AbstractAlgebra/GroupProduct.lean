/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.GroupAutomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 群的直积、内部直积与半直积

外直积 `G × H` 逐坐标运算；内部直积则把环境群中的两个子群识别成这两个坐标。
在前一模块已经定义 `Aut(N)` 后，半直积允许右因子通过一个同态
`φ : G → Aut(N)` 扭曲左因子的乘法，是直积的自然推广。
-/

namespace SandronesLibrary
namespace AbstractAlgebra.Group

/-- 交换两个直积因子得到群同构 `G × H ≃ H × G`。
> **Entry**: abstract-algebra.group.product-/
def directProductComm {G H : Type*} [Group G] [Group H] : G × H ≃* H × G :=
  MulEquiv.prodComm

/-- 直积在规范结合映射下满足结合律。
> **Entry**: abstract-algebra.group.product-/
def directProductAssoc {G H K : Type*} [Group G] [Group H] [Group K] :
    (G × H) × K ≃* G × (H × K) :=
  MulEquiv.prodAssoc

/-- 直积中分别来自两个因子的元素彼此交换。
> **Entry**: abstract-algebra.group.product
@isnad1 id=commute.0h4v.s7.a53a4c8de7ab from=translated src=- shape=47362464 vocab=90ce0c8e
-/
theorem directProduct_factors_commute {G H : Type*} [Group G] [Group H]
    (g : G) (h : H) :
    Commute (MonoidHom.inl G H g) (MonoidHom.inr G H h) := by
  exact MonoidHom.commute_inl_inr g h

/-- **内部直积定理**：若 `H`、`K` 逐元素交换，并且每个 `g : G` 都能唯一写成
`g = hk`，则坐标乘法给出群同构 `H × K ≃ G`。

`H.IsComplement' K` 精确记录乘法映射 `(h,k) ↦ hk` 的双射性，因此同时包含
`HK = G` 与分解唯一性（等价于经典条件 `H ∩ K = {1}`）。
> **Entry**: abstract-algebra.group.product-/
noncomputable def internalDirectProductEquiv {G : Type*} [Group G]
    (H K : Subgroup G)
    (hcomm : ∀ h : H, ∀ k : K, Commute (h : G) (k : G))
    (hcompl : H.IsComplement' K) : H × K ≃* G :=
  MulEquiv.ofBijective
    (MonoidHom.noncommCoprod H.subtype K.subtype hcomm) hcompl

/-- 内部直积同构按教材公式 `(h,k) ↦ hk` 工作。
> **Entry**: abstract-algebra.group.product
@isnad1 id=eq.2h4v.s9.3484aa2f1ea9 from=translated src=- shape=c309de91 vocab=8ccc0b02
-/
theorem internalDirectProductEquiv_apply {G : Type*} [Group G]
    (H K : Subgroup G)
    (hcomm : ∀ h : H, ∀ k : K, Commute (h : G) (k : G))
    (hcompl : H.IsComplement' K) (x : H × K) :
    internalDirectProductEquiv H K hcomm hcompl x = (x.1 : G) * (x.2 : G) := by
  rfl

/-- 半直积的乘法公式：`(n₁,g₁)(n₂,g₂)=(n₁ φ(g₁)(n₂),g₁g₂)`。
> **Entry**: abstract-algebra.group.product
@isnad1 id=eq.0h5v.s9.4e204bc0d6ad from=translated src=- shape=62f833b8 vocab=d99e28bc
-/
theorem semidirectProduct_mul {N G : Type*} [Group N] [Group G]
    (φ : G →* MulAut N) (x y : N ⋊[φ] G) :
    x * y = ⟨x.left * φ x.right y.left, x.right * y.right⟩ := by
  rfl

/-- 半直积中每个元素按坐标分解成左因子与右因子的乘积。
> **Entry**: abstract-algebra.group.product
@isnad1 id=eq.0h4v.s8.5f088131bd0f from=translated src=- shape=24542d7f vocab=2bcede68
-/
theorem semidirectProduct_decomposition {N G : Type*} [Group N] [Group G]
    (φ : G →* MulAut N) (x : N ⋊[φ] G) :
    SemidirectProduct.inl x.left * SemidirectProduct.inr x.right = x := by
  exact SemidirectProduct.inl_left_mul_inr_right x

/-- 平凡作用给出的半直积规范同构于通常直积。
> **Entry**: abstract-algebra.group.product-/
def trivialSemidirectProductEquiv {N G : Type*} [Group N] [Group G] :
    N ⋊[(1 : G →* MulAut N)] G ≃* N × G :=
  SemidirectProduct.mulEquivProd

/-- **内部半直积定理**：若正规子群 `H` 与子群 `K` 互补，则环境群同构于
由 `K` 在 `H` 上的共轭作用形成的半直积。
> **Entry**: abstract-algebra.group.product-/
noncomputable def internalSemidirectProductEquiv {G : Type*} [Group G]
    (H K : Subgroup G) [H.Normal] (h : H.IsComplement' K) :
    H ⋊[(H.normalizerMonoidHom).comp
      (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))] K ≃* G :=
  SemidirectProduct.mulEquivSubgroup h

/-- 内部半直积同构同样按坐标乘法 `(h,k) ↦ hk` 工作。
> **Entry**: abstract-algebra.group.product
@isnad1 id=eq.1h4v.s12.e7ef8084c24b from=translated src=- shape=b92de874 vocab=ede945c4
-/
theorem internalSemidirectProductEquiv_apply {G : Type*} [Group G]
    (H K : Subgroup G) [H.Normal] (h : H.IsComplement' K)
    (x : H ⋊[(H.normalizerMonoidHom).comp
      (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))] K) :
    internalSemidirectProductEquiv H K h x = (x.left : G) * (x.right : G) := by
  rfl

end AbstractAlgebra.Group
end SandronesLibrary
