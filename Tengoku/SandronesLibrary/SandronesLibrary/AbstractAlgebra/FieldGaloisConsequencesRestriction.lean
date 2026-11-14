/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldGaloisConsequencesNormality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / Galois 对应中的限制同态与商群

设 `L/K` 是有限 Galois 扩张，`H` 是 `Gal(L/K)` 的正规子群，`Lᴴ` 是
`H` 的固定域。本模块构造真正的群同态

`Gal(L/K) →* Gal(Lᴴ/K)`，

其函数值就是把环境自同构限制到固定域 carrier。随后证明该同态的核为
`H`、像为整个 `Gal(Lᴴ/K)`，并由群的第一同构定理得到教材公式

`Gal(L/K) ⧸ H ≃* Gal(Lᴴ/K)`。

公开子群承载一律使用 Mathlib `Subgroup`，不新增历史 `SubgroupSet` API。
Mathlib 的 `restrictNormalHom_surjective` 只在私有证明后端提供成熟的正规
限制满射；公开同态仍由本库 A3.9b 的 `restrictAutomorphism` 实际构造，
并给出逐点计算公式。因此商群同构不是对 Mathlib 最终同构的空包装。

> **Entry**: abstract-algebra.field.galois-restriction
-/

namespace SandronesLibrary.AbstractAlgebra.GaloisConsequencesRestriction

open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
open SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions
open SandronesLibrary.AbstractAlgebra.FieldGaloisCorrespondence
open SandronesLibrary.AbstractAlgebra.GaloisConsequencesDegreeIndex
open SandronesLibrary.AbstractAlgebra.GaloisConsequencesNormality

noncomputable local instance fieldAutomorphismOverGroup
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    Group (FieldAutomorphismOver e) := by
  let h := fieldAutomorphismOver_groupAxioms e
  exact Group.ofLeftAxioms h.mul_assoc h.one_mul h.inv_mul

-- Q01：正规子群固定域在每个环境自同构及其逆下稳定。
private theorem fixedField_preserves_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) (σ : FieldAutomorphismOver e) :
    PreservesIntermediateField σ (fixedFieldIntermediateField e H) := by
  constructor
  · intro x hx τ hτ
    have hconj : σ⁻¹ * τ * σ ∈ H := hH.conj_mem' τ hτ σ
    have hfixed := hx (σ⁻¹ * τ * σ) hconj
    have happly := congrArg σ.forward hfixed
    change
      σ.forward
          (SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ
            (τ.forward (σ.forward x))) = σ.forward x at happly
    rwa [σ.right_inverse] at happly
  · intro x hx τ hτ
    have hconj : σ * τ * σ⁻¹ ∈ H := by
      simpa using hH.conj_mem' τ hτ σ⁻¹
    have hfixed := hx (σ * τ * σ⁻¹) hconj
    have happly := congrArg
      (SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ)
      hfixed
    change
      SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ
          (σ.forward (τ.forward
            (SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ
              x))) =
        SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ x at happly
    rwa [σ.left_inverse] at happly

-- Q02：逐点限制保持恒等与乘法，因而组装为群同态。
private theorem fixedField_restriction_laws_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) :
    (restrictAutomorphism (fixedFieldIntermediateField e H) 1
        (fixedField_preserves_bridge e H hH 1) = 1) ∧
      ∀ σ τ : FieldAutomorphismOver e,
        restrictAutomorphism (fixedFieldIntermediateField e H) (σ * τ)
            (fixedField_preserves_bridge e H hH (σ * τ)) =
          restrictAutomorphism (fixedFieldIntermediateField e H) σ
              (fixedField_preserves_bridge e H hH σ) *
            restrictAutomorphism (fixedFieldIntermediateField e H) τ
              (fixedField_preserves_bridge e H hH τ) := by
  constructor
  · apply FieldAutomorphismOver.ext
    intro x
    exact restrictAutomorphism_identity_apply (fixedFieldIntermediateField e H) x
  · intro σ τ
    apply FieldAutomorphismOver.ext
    intro x
    exact restrictAutomorphism_comp_apply
      (fixedFieldIntermediateField e H) σ τ
      (fixedField_preserves_bridge e H hH σ)
      (fixedField_preserves_bridge e H hH τ) x

/-- **固定域限制同态**：把 `L/K` 的每个基域自同构限制到正规子群 `H`
的固定域 `Lᴴ`。正规性保证固定域在自同构及其逆下稳定；恒等与复合公式
保证这些逐点限制组成真正的群同态。

> **Entry**: abstract-algebra.field.galois-restriction-/
noncomputable def fixedFieldRestrictionHom
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) :
    FieldAutomorphismOver e →*
      FieldAutomorphismOver
        (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) :=
  { toFun := fun σ => restrictAutomorphism (fixedFieldIntermediateField e H) σ
      (fixedField_preserves_bridge e H hH σ)
    map_one' := (fixedField_restriction_laws_bridge e H hH).1
    map_mul' := (fixedField_restriction_laws_bridge e H hH).2 }

/-- 限制同态的逐点计算公式：在固定域元素 `x` 上，限制后的自同构与
原自同构 `σ` 具有相同的底层 `L` 中取值。

> **Entry**: abstract-algebra.field.galois-restriction-/
theorem fixedFieldRestrictionHom_apply
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) (σ : FieldAutomorphismOver e)
    (x : IntermediateFieldCarrier (fixedFieldIntermediateField e H)) :
    ((fixedFieldRestrictionHom e H hH σ).forward x).val = σ.forward x.val := by
  exact restrictAutomorphism_apply _ _ _ _

-- Q03：有限扩张恢复把限制同态的核严格识别为原子群。
private theorem fixedFieldRestrictionHom_ker_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) (hH : H.Normal) :
    (fixedFieldRestrictionHom e H hH).ker = H := by
  let F := fixedFieldIntermediateField e H
  have hrecover :
      FixingAutomorphismSet e (FixedFieldSet e (H : Set _)) = (H : Set _) :=
    congrArg
      (fun S : Subgroup (FieldAutomorphismOver e) =>
        (S : Set (FieldAutomorphismOver e)))
      (finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet e hfin H)
  ext σ
  rw [MonoidHom.mem_ker]
  change
    restrictAutomorphism F σ (fixedField_preserves_bridge e H hH σ) = 1 ↔
      σ ∈ H
  have hmem :
      σ ∈ FixingAutomorphismSet e F.carrier ↔ σ ∈ H := by
    simpa [F, fixedFieldIntermediateField] using
      (Set.ext_iff.mp hrecover σ)
  exact (fixing_iff_restrictAutomorphism_eq_identity F σ
    (fixedField_preserves_bridge e H hH σ)).symm.trans hmem

/-- 有限扩张中，固定域限制同态的核恰为 `H`。换言之，一个环境
自同构限制为恒等，当且仅当它逐点固定 `Lᴴ`，而有限 Galois 对应把这组
自同构恢复为原子群。

> **Entry**: abstract-algebra.field.galois-restriction-/
theorem fixedFieldRestrictionHom_ker
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) (hH : H.Normal) :
    (fixedFieldRestrictionHom e H hH).ker = H :=
  fixedFieldRestrictionHom_ker_bridge e hfin H hH

-- Q04：Mathlib 正规限制满射对齐到本库真实限制同态。
private theorem fixedFieldRestrictionHom_surjective_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) : Function.Surjective (fixedFieldRestrictionHom e H hH) := by
  let F := fixedFieldIntermediateField e H
  let _ : Algebra K (IntermediateFieldCarrier F) :=
    (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
  let _ : Algebra (IntermediateFieldCarrier F) L :=
    (intermediateFieldInclusion F).toRingHom.toAlgebra
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let _ : IsScalarTower K (IntermediateFieldCarrier F) L := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.algebraMap_toAlgebra]
    apply RingHom.ext
    intro x
    exact intermediateFieldBaseEmbedding_apply F x
  obtain ⟨⟨hfd⟩, ⟨hmg⟩⟩ := finiteGalois_mathlibBackend e hfin hgal
  let _ : FiniteDimensional K L := hfd
  let _ : IsGalois K L := hmg
  have hn : NormalExtension (intermediateFieldBaseEmbedding F) := by
    exact (subgroup_normal_iff_fixedField_normalExtension
      e hfin hgal H).mp hH
  let _ : Normal K (IntermediateFieldCarrier F) :=
    (normalExtension_iff_mathlibNormal
      (intermediateFieldBaseEmbedding F)).mp hn
  let φ := fieldAutomorphismOver_mathlibAlgEquiv_mulEquiv e
  let φF := fieldAutomorphismOver_mathlibAlgEquiv_mulEquiv
    (intermediateFieldBaseEmbedding F)
  intro y
  change FieldAutomorphismOver (intermediateFieldBaseEmbedding F) at y
  obtain ⟨g, hg⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := IntermediateFieldCarrier F) (E := L) (φF y)
  let σ := φ.symm g
  refine ⟨σ, ?_⟩
  apply φF.injective
  rw [← hg]
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change
    ((fixedFieldRestrictionHom e H hH σ).forward x).val =
      ((AlgEquiv.restrictNormalHom (IntermediateFieldCarrier F)) g x).val
  rw [fixedFieldRestrictionHom_apply]
  have hφσ : φ σ = g := φ.apply_symm_apply g
  have hpoint := congrArg (fun q : L ≃ₐ[K] L => q x.val) hφσ
  have hrestrict := AlgEquiv.restrictNormal_commutes
    g (IntermediateFieldCarrier F) x
  exact hpoint.trans hrestrict.symm

/-- 有限 Galois 扩张中，对正规子群固定域的限制同态是满射。每个
`K`-自同构 `Lᴴ → Lᴴ` 都能提升为 `L/K` 的自同构。

> **Entry**: abstract-algebra.field.galois-restriction-/
theorem fixedFieldRestrictionHom_surjective
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) : Function.Surjective (fixedFieldRestrictionHom e H hH) :=
  fixedFieldRestrictionHom_surjective_bridge e hfin hgal H hH

/-- 满射性的子群表述：固定域限制同态的 range 是整个固定域
自同构群 `⊤`。

> **Entry**: abstract-algebra.field.galois-restriction-/
theorem fixedFieldRestrictionHom_range
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) : (fixedFieldRestrictionHom e H hH).range = ⊤ :=
  MonoidHom.range_eq_top.mpr
    (fixedFieldRestrictionHom_surjective e hfin hgal H hH)

-- Q05：第一同构定理经核等式换写到商群 `G/H`，并保持投影公式。
private theorem fixedFieldQuotientEquiv_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) :
    letI : H.Normal := hH
    ∃ q : FieldAutomorphismOver e ⧸ H ≃*
        FieldAutomorphismOver
          (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)),
      ∀ σ : FieldAutomorphismOver e,
        q (QuotientGroup.mk σ) = fixedFieldRestrictionHom e H hH σ := by
  let _ : H.Normal := hH
  let f := fixedFieldRestrictionHom e H hH
  have hker : f.ker = H := fixedFieldRestrictionHom_ker e hfin H hH
  let qker : FieldAutomorphismOver e ⧸ f.ker ≃*
      FieldAutomorphismOver
        (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) :=
    QuotientGroup.quotientKerEquivOfSurjective f
      (fixedFieldRestrictionHom_surjective e hfin hgal H hH)
  let qchange : FieldAutomorphismOver e ⧸ H ≃*
      FieldAutomorphismOver e ⧸ f.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  refine ⟨qchange.trans qker, ?_⟩
  intro σ
  rfl

/-- **固定域商群同构**：有限 Galois 扩张中，环境 Galois 群模去正规
子群 `H`，同构于 `H` 的固定域在基域上的 Galois 群。这是第一同构定理
应用于真实限制同态所得的正式承载。

> **Entry**: abstract-algebra.field.galois-restriction-/
noncomputable def fixedFieldQuotientEquiv
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) :
    letI : H.Normal := hH
    FieldAutomorphismOver e ⧸ H ≃*
      FieldAutomorphismOver
        (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) :=
  Classical.choose (fixedFieldQuotientEquiv_bridge e hfin hgal H hH)

/-- 商群同构的自然投影公式：自同构 `σ` 的陪集映到 `σ` 在固定域上的
真实限制。该公式表明商群同构与前述 restriction hom 严格相容。

> **Entry**: abstract-algebra.field.galois-restriction-/
theorem fixedFieldQuotientEquiv_mk_apply
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e))
    (hH : H.Normal) (σ : FieldAutomorphismOver e) :
    letI : H.Normal := hH
    fixedFieldQuotientEquiv e hfin hgal H hH (QuotientGroup.mk σ) =
      fixedFieldRestrictionHom e H hH σ :=
  Classical.choose_spec
    (fixedFieldQuotientEquiv_bridge e hfin hgal H hH) σ

end SandronesLibrary.AbstractAlgebra.GaloisConsequencesRestriction
