/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Categorical.AlgebraicPullbacks
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Profinite.Basic
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.TopologicalGroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous pullbacks of topological groups

This module develops continuous fiber products and the universal property
obtained by testing a continuous square against profinite source groups. The
four objects in a tested square are not required to be profinite.
-/

namespace ProCGroups.Categorical

open CategoryTheory Limits

universe u v

section

open _root_.ProCGroups.ContinuousMonoidHom

variable {A G H H₁ H₂ K : Type u}

/-- Continuous pullback carrier attached to two continuous homomorphisms.-/
abbrev TopologicalFiberProduct.carrier
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :=
  FiberProduct.carrier (β₁ : H₁ →* H) (β₂ : H₂ →* H)

/-- The first projection from the continuous pullback.-/
def TopologicalFiberProduct.fst
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₁ :=
  { FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H) with
    continuous_toFun := continuous_fst.comp continuous_subtype_val }

/-- The second projection from the continuous pullback.-/
def TopologicalFiberProduct.snd
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    TopologicalFiberProduct.carrier β₁ β₂ →ₜ* H₂ :=
  { FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H) with
    continuous_toFun := continuous_snd.comp continuous_subtype_val }

/-- Extensionality for continuous homomorphisms into the concrete continuous fiber product.-/
theorem TopologicalFiberProduct.hom_ext
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    {ψ ψ' : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂}
    (h₁ : ∀ k, TopologicalFiberProduct.fst β₁ β₂ (ψ k) = TopologicalFiberProduct.fst β₁ β₂ (ψ' k))
    (h₂ : ∀ k, TopologicalFiberProduct.snd β₁ β₂ (ψ k) = TopologicalFiberProduct.snd β₁ β₂ (ψ' k)) :
    ψ = ψ' := by
  apply ContinuousMonoidHom.ext
  intro k
  exact Subtype.ext <| Prod.ext (h₁ k) (h₂ k)

/-- The canonical continuous map into the pullback.-/
def TopologicalFiberProduct.lift
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    K →ₜ* TopologicalFiberProduct.carrier β₁ β₂ :=
  { FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
      (φ₁ : K →* H₁) (φ₂ : K →* H₂) h with
    continuous_toFun := by
      exact Continuous.subtype_mk
        (φ₁.continuous_toFun.prodMk φ₂.continuous_toFun)
        (by
          intro k
          exact h k) }

/-- Composing the first projection with the continuous pullback lift gives \(\varphi_1\).-/
@[simp] theorem pullbackFstCont_pullbackLiftCont
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (TopologicalFiberProduct.fst β₁ β₂).comp (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₁ := by
  ext k
  rfl

/-- Composing the second projection with the continuous pullback lift gives \(\varphi_2\).-/
@[simp] theorem pullbackSndCont_pullbackLiftCont
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (TopologicalFiberProduct.snd β₁ β₂).comp (TopologicalFiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₂ := by
  ext k
  rfl

/-- The continuous pullback is reconstructed from its two projections by the canonical lift.-/
@[simp] theorem pullbackLiftCont_eta
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (ψ : K →ₜ* TopologicalFiberProduct.carrier β₁ β₂) :
    TopologicalFiberProduct.lift β₁ β₂
      ((TopologicalFiberProduct.fst β₁ β₂).comp ψ)
      ((TopologicalFiberProduct.snd β₁ β₂).comp ψ)
      (fun k => by exact (ψ k).2) = ψ := by
  apply TopologicalFiberProduct.hom_ext
  · intro k
    rfl
  · intro k
    rfl

/-- The concrete topological fiber product as a categorical pullback cone in TopGrp.-/
def TopologicalFiberProduct.cone
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [IsTopologicalGroup H] [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    PullbackCone (TopGrp.ofHom β₁) (TopGrp.ofHom β₂) :=
  PullbackCone.mk
    (TopGrp.ofHom (TopologicalFiberProduct.fst β₁ β₂))
    (TopGrp.ofHom (TopologicalFiberProduct.snd β₁ β₂))
    (by
      apply TopGrp.hom_ext
      ext x
      exact x.2)

/-- The concrete topological fiber product cone is a limit cone in TopGrp.-/
def TopologicalFiberProduct.isLimit
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [IsTopologicalGroup H] [IsTopologicalGroup H₁] [IsTopologicalGroup H₂]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    IsLimit (TopologicalFiberProduct.cone β₁ β₂) := by
  refine PullbackCone.IsLimit.mk (by
    apply TopGrp.hom_ext
    ext x
    exact x.2) ?lift ?fac_left ?fac_right ?uniq
  · intro s
    exact TopGrp.ofHom <|
      TopologicalFiberProduct.lift β₁ β₂ s.fst.hom s.snd.hom (fun x => by
        have hcondition :
            (s.fst ≫ TopGrp.ofHom β₁).hom =
              (s.snd ≫ TopGrp.ofHom β₂).hom :=
          congrArg (fun f : s.pt ⟶ TopGrp.of H => f.hom) s.condition
        exact DFunLike.congr_fun hcondition x)
  · intro s
    apply TopGrp.hom_ext
    rfl
  · intro s
    apply TopGrp.hom_ext
    rfl
  · intro s m hfst hsnd
    apply TopGrp.hom_ext
    ext x
    · have hfst' :
          (m ≫ TopGrp.ofHom (TopologicalFiberProduct.fst β₁ β₂)).hom = s.fst.hom :=
        congrArg (fun f : s.pt ⟶ TopGrp.of H₁ => f.hom) hfst
      exact DFunLike.congr_fun hfst' x
    · have hsnd' :
          (m ≫ TopGrp.ofHom (TopologicalFiberProduct.snd β₁ β₂)).hom = s.snd.hom :=
        congrArg (fun f : s.pt ⟶ TopGrp.of H₂ => f.hom) hsnd
      exact DFunLike.congr_fun hsnd' x

/--
Continuous pullback property tested by profinite source objects. The property tests the square
against profinite objects without requiring the four objects of the square themselves to be
profinite.-/
def HasProfiniteTestPullbackProperty
    [Group G] [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    (α₁ : G →ₜ* H₁) (α₂ : G →ₜ* H₂)
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) : Prop :=
  β₁.comp α₁ = β₂.comp α₂ ∧
    ∀ ⦃K : Type u⦄ [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
      [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K],
      ∀ (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂),
      β₁.comp φ₁ = β₂.comp φ₂ →
      ∃! φ : K →ₜ* G, α₁.comp φ = φ₁ ∧ α₂.comp φ = φ₂

/-- Chosen continuous morphism induced by the pullback universal property.-/
noncomputable def pullbackDescCont
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) : K →ₜ* G :=
  Classical.choose (ExistsUnique.exists (hpb.2 (K := K) φ₁ φ₂ hφ))

/-- Specification of the chosen continuous pullback descent map.-/
theorem pullbackDescCont_spec
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₁.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₁ ∧
      α₂.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₂ :=
  Classical.choose_spec (ExistsUnique.exists (hpb.2 (K := K) φ₁ φ₂ hφ))

/-- The left composite of the chosen continuous pullback descent map is the prescribed left leg.-/
@[simp] theorem pullbackDescCont_left
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₁.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₁ :=
  (pullbackDescCont_spec hpb φ₁ φ₂ hφ).1

/--
The right composite of the chosen continuous pullback descent map is the prescribed right leg.-/
@[simp] theorem pullbackDescCont_right
    [Group G] [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    {α₁ : G →ₜ* H₁} {α₂ : G →ₜ* H₂}
    {β₁ : H₁ →ₜ* H} {β₂ : H₂ →ₜ* H}
    (hpb : HasProfiniteTestPullbackProperty α₁ α₂ β₁ β₂)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (hφ : β₁.comp φ₁ = β₂.comp φ₂) :
    α₂.comp (pullbackDescCont hpb φ₁ φ₂ hφ) = φ₂ :=
  (pullbackDescCont_spec hpb φ₁ φ₂ hφ).2

/-- The concrete pullback subgroup is closed in \(H_1 \times H_2\).-/
theorem pullback_isClosed
    {H H₁ H₂ : Type u}
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [T2Space H]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H) :
    IsClosed ((FiberProduct.subgroup (β₁ : H₁ →* H) (β₂ : H₂ →* H) : Subgroup (H₁ × H₂)) :
      Set (H₁ × H₂)) := by
  change IsClosed { x : H₁ × H₂ | β₁ x.1 = β₂ x.2 }
  exact isClosed_eq (β₁.continuous_toFun.comp continuous_fst)
    (β₂.continuous_toFun.comp continuous_snd)

/-- The concrete pullback of continuous maps between compact Hausdorff groups is compact.-/
noncomputable instance TopologicalFiberProduct.compactSpace
    {H H₁ H₂ : Type u}
    [Group H] [Group H₁] [Group H₂]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
    [CompactSpace H₁] [CompactSpace H₂] [T2Space H]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    : CompactSpace (TopologicalFiberProduct.carrier β₁ β₂) := by
  apply isCompact_iff_compactSpace.1
  simpa [TopologicalFiberProduct.carrier, FiberProduct.carrier] using
    (pullback_isClosed β₁ β₂).isCompact

namespace TopologicalFiberProduct

/-- Composing the first projection with a topological fiber-product lift gives the left map.-/
@[simp] theorem fst_lift
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (fst β₁ β₂).comp (lift β₁ β₂ φ₁ φ₂ h) = φ₁ :=
  pullbackFstCont_pullbackLiftCont β₁ β₂ φ₁ φ₂ h

/-- Composing the second projection with a topological fiber-product lift gives the right map.-/
@[simp] theorem snd_lift
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (snd β₁ β₂).comp (lift β₁ β₂ φ₁ φ₂ h) = φ₂ :=
  pullbackSndCont_pullbackLiftCont β₁ β₂ φ₁ φ₂ h

/-- The first projection of a lifted element is the value of the first coordinate map.-/
@[simp] theorem fst_lift_apply
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    fst β₁ β₂ (lift β₁ β₂ φ₁ φ₂ h k) = φ₁ k :=
  rfl

/-- The second projection of a lifted element is the value of the second coordinate map.-/
@[simp] theorem snd_lift_apply
    [Group H] [Group H₁] [Group H₂] [Group K]
    [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace K]
    (β₁ : H₁ →ₜ* H) (β₂ : H₂ →ₜ* H)
    (φ₁ : K →ₜ* H₁) (φ₂ : K →ₜ* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) (k : K) :
    snd β₁ β₂ (lift β₁ β₂ φ₁ φ₂ h k) = φ₂ k :=
  rfl

end TopologicalFiberProduct

end

end ProCGroups.Categorical
