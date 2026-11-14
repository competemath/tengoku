/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldGaloisConsequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / Galois 对应中的正规子群

在有限 Galois 扩张 `L/K` 中，中间域 `F` 对应逐点固定它的自同构子群。
本模块证明这一对应的正规性部分：正式子群 `H` 正规，当且仅当固定域
`Lᴴ/K` 是 Galois 扩张；由于该固定域子扩张自动可分，这又等价于它是
正规扩张。

证明只在私有后端把本库显式嵌入和固定域 carrier 对齐到 Mathlib 的
`AlgEquiv`、`Subgroup` 与 `IntermediateField`。自同构群乘法等价、有限
Galois 后端以及可分／正规扩张语义桥全部复用下层已验证接口，不重复
构造最小多项式或分裂证明。

> **Entry**: abstract-algebra.field.galois-normality
-/

namespace SandronesLibrary.AbstractAlgebra.GaloisConsequencesNormality

open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSplitting
open SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
open SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions
open SandronesLibrary.AbstractAlgebra.FieldGaloisCorrespondence
open SandronesLibrary.AbstractAlgebra.GaloisConsequencesDegreeIndex

noncomputable local instance fieldAutomorphismOverGroup
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    Group (FieldAutomorphismOver e) := by
  let h := fieldAutomorphismOver_groupAxioms e
  exact Group.ofLeftAxioms h.mul_assoc h.one_mul h.inv_mul

private theorem fixedField_mathlib_alignment_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e)) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∃ (φ : FieldAutomorphismOver e ≃* (L ≃ₐ[K] L))
      (G : Subgroup (L ≃ₐ[K] L)) (E : IntermediateField K L),
      (∀ σ, σ ∈ H ↔ φ σ ∈ G) ∧
        (E : Set L) = FixedFieldSet e (H : Set (FieldAutomorphismOver e)) ∧
        E = IntermediateField.fixedField G := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let φ := fieldAutomorphismOver_mathlibAlgEquiv_mulEquiv e
  let G : Subgroup (L ≃ₐ[K] L) := H.map φ.toMonoidHom
  let E : IntermediateField K L := IntermediateField.fixedField G
  refine ⟨φ, G, E, ?_, ?_, rfl⟩
  · intro σ
    constructor
    · intro hσ
      exact ⟨σ, hσ, rfl⟩
    · rintro ⟨τ, hτ, hτσ⟩
      have : τ = σ := φ.injective hτσ
      rwa [← this]
  · ext x
    constructor
    · intro hx σ hσ
      have hφσ : φ σ ∈ G := ⟨σ, hσ, rfl⟩
      change x ∈ IntermediateField.fixedField G at hx
      exact (IntermediateField.mem_fixedField_iff G x).mp hx (φ σ) hφσ
    · intro hx
      change x ∈ IntermediateField.fixedField G
      apply (IntermediateField.mem_fixedField_iff G x).mpr
      intro g hg
      obtain ⟨σ, hσ, rfl⟩ := hg
      exact hx σ hσ

private theorem subgroup_normal_alignment_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e)) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∀ (φ : FieldAutomorphismOver e ≃* (L ≃ₐ[K] L))
      (G : Subgroup (L ≃ₐ[K] L)),
      (∀ σ, σ ∈ H ↔ φ σ ∈ G) → (H.Normal ↔ G.Normal) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  intro φ G hHG
  have hmap : H.map φ.toMonoidHom = G := by
    ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (hHG σ).mp hσ
    · intro hg
      refine ⟨φ.symm g, (hHG (φ.symm g)).mpr ?_, ?_⟩
      · simpa using hg
      · exact φ.apply_symm_apply g
  rw [← hmap]
  exact (MulEquiv.normal_map_iff (f := φ) (H := H)).symm

private noncomputable def fixedFieldCarrierAlgEquivMathlib
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (M : IntermediateField K L)
    (hM : (M : Set L) = F.carrier)
    (hAlg : algebraMap K L = e.toRingHom) :
    letI : Algebra K (IntermediateFieldCarrier F) :=
      (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
    IntermediateFieldCarrier F ≃ₐ[K] M := by
  let _ : Algebra K (IntermediateFieldCarrier F) :=
    (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
  refine
    { toFun := fun x => ⟨x.val, (Set.ext_iff.mp hM x.val).mpr x.property⟩
      invFun := fun x => ⟨x.val, (Set.ext_iff.mp hM x.val).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      commutes' := ?_ }
  intro c
  apply Subtype.ext
  change
    intermediateFieldInclusion F (intermediateFieldBaseEmbedding F c) =
      algebraMap K L c
  rw [intermediateFieldBaseEmbedding_apply F, hAlg]
  rfl

private theorem fixedField_galois_alignment_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Subgroup (FieldAutomorphismOver e)) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∀ (E : IntermediateField K L),
      (E : Set L) = FixedFieldSet e (H : Set (FieldAutomorphismOver e)) →
      (GaloisExtension
          (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) ↔
        IsGalois K E) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  intro E hE
  let F := fixedFieldIntermediateField e H
  have hEF : (E : Set L) = F.carrier := hE.trans (by rfl)
  change GaloisExtension (intermediateFieldBaseEmbedding F) ↔ IsGalois K E
  let _ : Algebra K (IntermediateFieldCarrier F) :=
    (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
  have hbackend :
      GaloisExtension (intermediateFieldBaseEmbedding F) ↔
        IsGalois K (IntermediateFieldCarrier F) := by
    rw [GaloisExtension, isGalois_iff,
      separableExtension_iff_mathlibIsSeparable,
      normalExtension_iff_mathlibNormal]
  let ψ := fixedFieldCarrierAlgEquivMathlib F E hEF
    (RingHom.algebraMap_toAlgebra e.toRingHom)
  exact hbackend.trans ψ.transfer_galois

private theorem mathlib_normal_iff_fixedField_isGalois_bridge
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G : Subgroup (L ≃ₐ[K] L)) :
    G.Normal ↔ IsGalois K (IntermediateField.fixedField G) := by
  constructor
  · intro hnormal
    let _ : G.Normal := hnormal
    exact IsGalois.of_fixedField_normal_subgroup G
  · intro hgalois
    let _ : IsGalois K (IntermediateField.fixedField G) := hgalois
    have hnormal :
        (IntermediateField.fixedField G).fixingSubgroup.Normal :=
      IsGalois.fixingSubgroup_normal_of_isGalois
        (IntermediateField.fixedField G)
    rw [IntermediateField.fixingSubgroup_fixedField G] at hnormal
    exact hnormal

private theorem fixedField_separableExtension_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e)) :
    SeparableExtension
      (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨⟨hfd⟩, ⟨hmg⟩⟩ := finiteGalois_mathlibBackend e hfin hgal
  let _ : FiniteDimensional K L := hfd
  let _ : IsGalois K L := hmg
  obtain ⟨φ, G, E, _hHG, hE, hfixed⟩ :=
    fixedField_mathlib_alignment_bridge e H
  let F := fixedFieldIntermediateField e H
  have hEF : (E : Set L) = F.carrier := hE.trans (by rfl)
  have hsep : Algebra.IsSeparable K E := by
    rw [hfixed]
    exact Algebra.isSeparable_tower_bot_of_isSeparable
      K (IntermediateField.fixedField G) L
  let _ : Algebra K (IntermediateFieldCarrier F) :=
    (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
  let ψ := fixedFieldCarrierAlgEquivMathlib F E hEF
    (RingHom.algebraMap_toAlgebra e.toRingHom)
  have hsepCarrier : Algebra.IsSeparable K (IntermediateFieldCarrier F) :=
    Algebra.IsSeparable.of_algHom K E ψ
  exact (separableExtension_iff_mathlibIsSeparable
    (intermediateFieldBaseEmbedding F)).mpr hsepCarrier

/-- 有限 Galois 扩张中，正式自同构子群正规，当且仅当其固定域在基域上
构成 Galois 扩张。

> **Entry**: abstract-algebra.field.galois-normality
@isnad1 id=iff.2h4v.s6.cba805620c12 from=translated src=- shape=a2eb655a vocab=46a26020
-/
theorem subgroup_normal_iff_fixedField_galoisExtension
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e)) :
    H.Normal ↔
      GaloisExtension
        (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨⟨hfd⟩, ⟨hmg⟩⟩ := finiteGalois_mathlibBackend e hfin hgal
  let _ : FiniteDimensional K L := hfd
  let _ : IsGalois K L := hmg
  obtain ⟨φ, G, E, hHG, hE, hfixed⟩ :=
    fixedField_mathlib_alignment_bridge e H
  rw [subgroup_normal_alignment_bridge e H φ G hHG]
  rw [fixedField_galois_alignment_bridge e H E hE]
  rw [hfixed]
  exact mathlib_normal_iff_fixedField_isGalois_bridge G

/-- 有限 Galois 扩张中，正式自同构子群正规，当且仅当其固定域在基域上
正规。固定域子扩张的可分性由环境有限 Galois 性自动提供。

> **Entry**: abstract-algebra.field.galois-normality
@isnad1 id=iff.2h4v.s6.888a91ed4b05 from=translated src=- shape=5dfa8a74 vocab=5333fad5
-/
theorem subgroup_normal_iff_fixedField_normalExtension
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (H : Subgroup (FieldAutomorphismOver e)) :
    H.Normal ↔
      NormalExtension
        (intermediateFieldBaseEmbedding (fixedFieldIntermediateField e H)) := by
  constructor
  · intro hH
    exact (subgroup_normal_iff_fixedField_galoisExtension
      e hfin hgal H).mp hH |>.isNormal
  · intro hn
    apply (subgroup_normal_iff_fixedField_galoisExtension e hfin hgal H).mpr
    exact ⟨fixedField_separableExtension_bridge e hfin hgal H, hn⟩

end SandronesLibrary.AbstractAlgebra.GaloisConsequencesNormality
