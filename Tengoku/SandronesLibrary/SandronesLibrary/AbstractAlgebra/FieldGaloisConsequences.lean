/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldGaloisCorrespondence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/FieldGaloisConsequences.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 有限 Galois 对应的次数—指数公式

本模块开始 A3.9c 的一般推论层。对有限 Galois 扩张 `L/K` 及其自同构群的
正式子群 `H`，先把 `H` 的共同固定点打包为显式中间域 `Lᴴ`，再证明两项
教材中的数值公式：

* `[L : Lᴴ] = |H|`；
* `[Lᴴ : K] = [Gal(L/K) : H]`。

证明不重新建立 Galois 对应。第一式复用 A3.9b 的子群恢复与 fixing 群阶—
相对次数公式；第二式把第一式、扩张塔次数乘法、全自同构群阶等于
总次数，
以及群论 Lagrange 公式组装起来，并以 `|H| > 0` 消去公共因子。

公开子群载体使用 Mathlib `Subgroup`；A3.9b 的历史 `SubgroupSet` 签名只在
证明体中通过兼容桥调用。本文件不包含二次扩张、有限域或低次多项式
算例，
也不进入正规子群、限制同态与商群批次。

> **Entry**: abstract-algebra.field.galois-consequences
-/

namespace SandronesLibrary.AbstractAlgebra.GaloisConsequencesDegreeIndex

open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSplitting
open SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions
open SandronesLibrary.AbstractAlgebra.FieldGaloisCorrespondence
open SandronesLibrary.AbstractAlgebra.Group

noncomputable local instance fieldAutomorphismOverGroup
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    Group (FieldAutomorphismOver e) := by
  let h := fieldAutomorphismOver_groupAxioms e
  exact Group.ofLeftAxioms h.mul_assoc h.one_mul h.inv_mul

/-- 正式自同构子群 `H` 的共同固定点构成显式中间域。其 carrier 按定义是
`FixedFieldSet e (H : Set _)`，而域运算封闭性由固定域的一般封闭定理给出。

> **Entry**: abstract-algebra.field.galois-consequences-/
noncomputable def fixedFieldIntermediateField
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L)
    (H : Subgroup (FieldAutomorphismOver e)) :
    ExplicitIntermediateField e :=
  ⟨FixedFieldSet e (H : Set (FieldAutomorphismOver e)),
    fixedFieldSet_isIntermediateField e H⟩

/-- 有限 Galois 扩张中，`L` 在 `H` 的固定域上的相对次数等于 `H` 的阶：
`[L : Lᴴ] = |H|`。

证明先用 A3.9b 得到相对次数等于 fixing 自同构集合的基数，再用有限
扩张中的
子群恢复把该 fixing 集合识别回 `H`。公开签名直接接受正式子群。

> **Entry**: abstract-algebra.field.galois-consequences
@isnad1 id=hasexten.2h4v.s7.4d7461de1ce6 from=translated src=- shape=71b8a3e4 vocab=524737c9
-/
theorem finiteGalois_fixedField_relativeDegree_eq_card
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    HasExtensionDegree
      (intermediateFieldInclusion (fixedFieldIntermediateField e H))
      (Nat.card H) := by
  let F := fixedFieldIntermediateField e H
  obtain ⟨n, hn, hcard⟩ :=
    finiteGalois_fixing_card_eq_relativeDegree e hfin hgal F
  have hfix :
      FixingAutomorphismSet e F.carrier =
        (H : Set (FieldAutomorphismOver e)) := by
    have hrecover :=
      finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet e hfin H
    have hcarrier := congrArg
      (fun S : Subgroup (FieldAutomorphismOver e) =>
        (S : Set (FieldAutomorphismOver e))) hrecover
    simpa [F, fixedFieldIntermediateField] using hcarrier
  have hcardH : Nat.card H = n := by
    rw [hfix] at hcard
    simpa using hcard
  exact hcardH.symm ▸ hn

private theorem hasExtensionDegree_mathlibBasis_bridge
    {A B : Type*} [Field A] [Field B] (j : FieldEmbedding A B)
    (n : ℕ) (h : HasExtensionDegree j n) :
    letI : Algebra A B := j.toRingHom.toAlgebra
    Nonempty (Module.Basis (Fin n) A B) := by
  let _ : Algebra A B := j.toRingHom.toAlgebra
  obtain ⟨v, hv⟩ := h
  have hsum (c : Fin n → A) :
      fieldLinearCombination j Finset.univ c v = ∑ i, c i • v i := by
    simp only [fieldLinearCombination, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, FieldEmbedding.toRingHom]
    rfl
  have hli : LinearIndependent A v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    apply hv.1 c
    rw [hsum]
    exact hc
  have hspan : Submodule.span A (Set.range v) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨c, hc⟩ := hv.2 x
    apply (Submodule.mem_span_range_iff_exists_fun A).mpr
    refine ⟨c, ?_⟩
    rw [← hsum]
    exact hc
  exact ⟨Module.Basis.mk hli hspan.ge⟩

private theorem hasExtensionDegree_of_finrank_bridge
    {A B : Type*} [Field A] [Field B] (j : FieldEmbedding A B)
    (n : ℕ) :
    letI : Algebra A B := j.toRingHom.toAlgebra
    FiniteDimensional A B → Module.finrank A B = n →
      HasExtensionDegree j n := by
  let _ : Algebra A B := j.toRingHom.toAlgebra
  intro hfd hrank
  let _ : FiniteDimensional A B := hfd
  let B₀ : Module.Basis (Fin n) A B := Module.finBasisOfFinrankEq A B hrank
  have hsum (c : Fin n → A) :
      fieldLinearCombination j Finset.univ c B₀ = ∑ i, c i • B₀ i := by
    simp only [fieldLinearCombination, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, FieldEmbedding.toRingHom]
    rfl
  refine ⟨fun i => B₀ i, ?_, ?_⟩
  · intro c hc i
    apply Fintype.linearIndependent_iff.mp B₀.linearIndependent c
    rw [← hsum]
    exact hc
  · intro x
    have hx : x ∈ Submodule.span A (Set.range fun i => B₀ i) := by
      rw [B₀.span_eq]
      trivial
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun A).mp hx
    refine ⟨c, ?_⟩
    rw [hsum]
    exact hc

private theorem intermediateField_baseDegree_exists_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (F : ExplicitIntermediateField e) :
    ∃ m : ℕ, HasExtensionDegree (intermediateFieldBaseEmbedding F) m := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨d, hd⟩ := hfin
  let B : Module.Basis (Fin d) K L :=
    Classical.choice (hasExtensionDegree_mathlibBasis_bridge e d hd)
  letI : FiniteDimensional K L := Module.Finite.of_basis B
  letI algKF : Algebra K (IntermediateFieldCarrier F) :=
    (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
  letI moduleKF : Module K (IntermediateFieldCarrier F) :=
    @Algebra.toModule K (IntermediateFieldCarrier F) _ _ algKF
  let ι : IntermediateFieldCarrier F →ₗ[K] L :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c x
        change (intermediateFieldBaseEmbedding F c).val * x.val = e c * x.val
        exact congrArg (fun z => z * x.val)
          (intermediateFieldBaseEmbedding_apply F c) }
  let finiteKF : @Module.Finite K (IntermediateFieldCarrier F) _ _ moduleKF :=
    Module.Finite.of_injective ι Subtype.val_injective
  letI : @Module.Finite K (IntermediateFieldCarrier F) _ _ moduleKF := finiteKF
  let hfd : @FiniteDimensional K (IntermediateFieldCarrier F) _ _ moduleKF :=
    finiteKF
  let m := Module.finrank K (IntermediateFieldCarrier F)
  refine ⟨m, ?_⟩
  exact hasExtensionDegree_of_finrank_bridge
    (intermediateFieldBaseEmbedding F) m hfd rfl

private theorem fixedField_baseDegree_exists_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    ∃ m : ℕ,
      HasExtensionDegree
        (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) m :=
  intermediateField_baseDegree_exists_bridge e hfin
    (fixedFieldIntermediateField e H)

private theorem fieldEmbedding_ext
    {K L : Type*} [Field K] [Field L]
    {e f : FieldEmbedding K L} (h : ∀ x, e x = f x) : e = f := by
  cases e with
  | mk et eh ei =>
    cases f with
    | mk ft fh fi =>
      change ∀ x, et x = ft x at h
      have heft : et = ft := funext h
      subst ft
      rfl

private theorem intermediate_extensionDegree_tower_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (F : ExplicitIntermediateField e)
    {m n : ℕ}
    (hm : HasExtensionDegree (intermediateFieldBaseEmbedding F) m)
    (hn : HasExtensionDegree (intermediateFieldInclusion F) n) :
    HasExtensionDegree e (m * n) := by
  have htower :=
    extensionDegree_tower
      (intermediateFieldBaseEmbedding F)
      (intermediateFieldInclusion F) hm hn
  have hcomp :
      (intermediateFieldInclusion F).comp
          (intermediateFieldBaseEmbedding F) = e := by
    apply fieldEmbedding_ext
    intro x
    exact intermediateFieldBaseEmbedding_apply F x
  exact hcomp ▸ htower

/-- 有限 Galois 扩张中，`H` 的固定域在基域上的次数等于 `H` 在全 Galois
群中的指数：`[Lᴴ : K] = [Gal(L/K) : H]`。

若该次数为 `m`，扩张塔公式和上一条定理给出 `m |H| = [L : K]`；A3.9b
的总次数公式把右端识别为全自同构群阶，而 Lagrange 公式给出
`|H| [G : H] = |G|`。由于相对次数 `|H|` 严格为正，可消去公共因子。

> **Entry**: abstract-algebra.field.galois-consequences
@isnad1 id=hasexten.2h4v.s6.5ef076574d6b from=translated src=- shape=d2a08554 vocab=4c48e6a3
-/
theorem finiteGalois_fixedField_degree_eq_index
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    HasExtensionDegree
      (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H))
      H.index := by
  let F := fixedFieldIntermediateField e H
  obtain ⟨m, hm⟩ := fixedField_baseDegree_exists_bridge e hfin H
  have hrelative :
      HasExtensionDegree (intermediateFieldInclusion F) (Nat.card H) := by
    simpa [F] using
      finiteGalois_fixedField_relativeDegree_eq_card e hfin hgal H
  have htower : HasExtensionDegree e (m * Nat.card H) :=
    intermediate_extensionDegree_tower_bridge e F hm hrelative
  obtain ⟨d, hd⟩ := hfin
  have hproduct :
      m * Nat.card H = Nat.card (FieldAutomorphismOver e) := by
    exact (extensionDegree_unique e htower hd).trans
      (finiteGalois_automorphism_card_eq_degree e hgal hd).symm
  have hlagrange :
      Nat.card H * H.index = Nat.card (FieldAutomorphismOver e) :=
    lagrange H
  have hcancel : Nat.card H * m = Nat.card H * H.index := by
    calc
      Nat.card H * m = m * Nat.card H := Nat.mul_comm _ _
      _ = Nat.card (FieldAutomorphismOver e) := hproduct
      _ = Nat.card H * H.index := hlagrange.symm
  have hcardPositive : 0 < Nat.card H :=
    extensionDegree_pos (intermediateFieldInclusion F) hrelative
  have hmindex : m = H.index :=
    Nat.eq_of_mul_eq_mul_left hcardPositive hcancel
  exact hmindex ▸ hm

end SandronesLibrary.AbstractAlgebra.GaloisConsequencesDegreeIndex
