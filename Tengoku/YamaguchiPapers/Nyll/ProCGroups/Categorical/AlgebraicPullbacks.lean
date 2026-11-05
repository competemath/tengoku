/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Category.Grp.Limits
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pro C Groups / Categorical / Algebraic Pullbacks

This module develops concrete fiber products of groups, identifies them with
the categorical pullback in `GrpCat`, and proves comparison and kernel
criteria for the associated lift maps.
-/

namespace ProCGroups.Categorical

open CategoryTheory Limits
open scoped Pointwise

universe u v

section

variable {A G H H₁ H₂ : Type u} {K : Type v}
variable [Group A] [Group G] [Group H] [Group H₁] [Group H₂] [Group K]

/-- Concrete pullback subgroup of \(\beta_1\) and \(\beta_2\).-/
def FiberProduct.subgroup (β₁ : H₁ →* H) (β₂ : H₂ →* H) : Subgroup (H₁ × H₂) where
  carrier := { x | β₁ x.1 = β₂ x.2 }
  one_mem' := by simp only [Set.mem_ofPred_eq, Prod.fst_one, map_one, Prod.snd_one]
  mul_mem' := by
    intro x y hx hy
    change β₁ x.1 = β₂ x.2 at hx
    change β₁ y.1 = β₂ y.2 at hy
    simpa [map_mul] using congrArg₂ (· * ·) hx hy
  inv_mem' := by
    intro x hx
    simpa [map_inv, hx]

/-- Concrete pullback attached to \(\beta_1\) and \(\beta_2\).-/
abbrev FiberProduct.carrier (β₁ : H₁ →* H) (β₂ : H₂ →* H) :=
  ↥(FiberProduct.subgroup β₁ β₂)

/-- Membership in the pullback subgroup is equivalent to the displayed coordinate condition.-/
@[simp] theorem mem_pullbackSubgroup_iff {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {x : H₁ × H₂} :
    x ∈ FiberProduct.subgroup β₁ β₂ ↔ β₁ x.1 = β₂ x.2 :=
  Iff.rfl

/-- The first projection from the concrete pullback.-/
def FiberProduct.fst (β₁ : H₁ →* H) (β₂ : H₂ →* H) : FiberProduct.carrier β₁ β₂ →* H₁ where
  toFun := fun x => x.1.1
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The second projection from the concrete pullback.-/
def FiberProduct.snd (β₁ : H₁ →* H) (β₂ : H₂ →* H) : FiberProduct.carrier β₁ β₂ →* H₂ where
  toFun := fun x => x.1.2
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The canonical homomorphism into the concrete pullback.-/
def FiberProduct.lift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) : K →* FiberProduct.carrier β₁ β₂ where
  toFun := fun k => ⟨(φ₁ k, φ₂ k), h k⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, OneMemClass.coe_one, Prod.mk_eq_one, and_self]
  map_mul' := by
    intro x y
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, Prod.mk_mul_mk]

/-- The concrete group pullback as a categorical pullback cone in GrpCat.-/
def FiberProduct.cone (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    PullbackCone (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
  PullbackCone.mk
    (GrpCat.ofHom (FiberProduct.fst β₁ β₂))
    (GrpCat.ofHom (FiberProduct.snd β₁ β₂))
    (by
      apply GrpCat.hom_ext
      ext x
      exact x.2)

/-- The concrete group pullback cone is a limit cone in GrpCat.-/
def FiberProduct.isLimitCone (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    IsLimit (FiberProduct.cone β₁ β₂) := by
  refine PullbackCone.IsLimit.mk (by
    apply GrpCat.hom_ext
    ext x
    exact x.2) ?lift ?fac_left ?fac_right ?uniq
  · intro s
    exact GrpCat.ofHom <|
      FiberProduct.lift β₁ β₂ s.fst.hom s.snd.hom (fun x => by
        have hcondition :
            (s.fst ≫ GrpCat.ofHom β₁).hom =
              (s.snd ≫ GrpCat.ofHom β₂).hom :=
          congrArg (fun f : s.pt ⟶ GrpCat.of H => f.hom) s.condition
        exact DFunLike.congr_fun hcondition x)
  · intro s
    apply GrpCat.hom_ext
    rfl
  · intro s
    apply GrpCat.hom_ext
    rfl
  · intro s m hfst hsnd
    apply GrpCat.hom_ext
    ext x
    · have hfst' :
          (m ≫ GrpCat.ofHom (FiberProduct.fst β₁ β₂)).hom = s.fst.hom :=
        congrArg (fun f : s.pt ⟶ GrpCat.of H₁ => f.hom) hfst
      exact DFunLike.congr_fun hfst' x
    · have hsnd' :
          (m ≫ GrpCat.ofHom (FiberProduct.snd β₁ β₂)).hom = s.snd.hom :=
        congrArg (fun f : s.pt ⟶ GrpCat.of H₂ => f.hom) hsnd
      exact DFunLike.congr_fun hsnd' x

/-- The concrete group fiber product is a pullback in mathlib's bundled category of groups.-/
theorem FiberProduct.isPullback (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    CategoryTheory.IsPullback
      (GrpCat.ofHom (FiberProduct.fst β₁ β₂))
      (GrpCat.ofHom (FiberProduct.snd β₁ β₂))
      (GrpCat.ofHom β₁) (GrpCat.ofHom β₂) :=
  CategoryTheory.IsPullback.of_isLimit (FiberProduct.isLimitCone β₁ β₂)

/--
The kernel of the canonical map into a concrete pullback is the intersection of the two
coordinate kernels.-/
@[simp] theorem ker_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.lift β₁ β₂ φ₁ φ₂ h).ker = φ₁.ker ⊓ φ₂.ker := by
  ext k
  change FiberProduct.lift β₁ β₂ φ₁ φ₂ h k = 1 ↔ φ₁ k = 1 ∧ φ₂ k = 1
  constructor
  · intro hk
    exact ⟨congrArg (fun z => FiberProduct.fst β₁ β₂ z) hk,
      congrArg (fun z => FiberProduct.snd β₁ β₂ z) hk⟩
  · rintro ⟨h₁, h₂⟩
    apply Subtype.ext
    exact Prod.ext h₁ h₂

/-- Composing the first projection with the canonical pullback lift gives \(\varphi_1\).-/
@[simp] theorem pullbackFst_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.fst β₁ β₂).comp (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₁ := by
  ext k
  rfl

/-- Composing the second projection with the canonical pullback lift gives \(\varphi_2\).-/
@[simp] theorem pullbackSnd_pullbackLift (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (φ₁ : K →* H₁) (φ₂ : K →* H₂)
    (h : ∀ k, β₁ (φ₁ k) = β₂ (φ₂ k)) :
    (FiberProduct.snd β₁ β₂).comp (FiberProduct.lift β₁ β₂ φ₁ φ₂ h) = φ₂ := by
  ext k
  rfl

/-- Two homomorphisms into the concrete pullback are equal once both coordinates agree.-/
theorem FiberProduct.hom_ext {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    {ψ ψ' : K →* FiberProduct.carrier β₁ β₂}
    (h₁ : ∀ k, FiberProduct.fst β₁ β₂ (ψ k) = FiberProduct.fst β₁ β₂ (ψ' k))
    (h₂ : ∀ k, FiberProduct.snd β₁ β₂ (ψ k) = FiberProduct.snd β₁ β₂ (ψ' k)) :
    ψ = ψ' := by
  apply MonoidHom.ext
  intro k
  exact Subtype.ext <| Prod.ext (h₁ k) (h₂ k)

namespace FiberProduct

/-- Transport a concrete fiber product across equal cospan maps.-/
def congr {β₁ β₁' : H₁ →* H} {β₂ β₂' : H₂ →* H}
    (h₁ : β₁ = β₁') (h₂ : β₂ = β₂') :
    carrier β₁ β₂ ≃* carrier β₁' β₂' := by
  subst β₁'
  subst β₂'
  exact MulEquiv.refl _

end FiberProduct

/-- The concrete pullback is reconstructed from its two projections by the canonical lift.-/
@[simp 900] theorem pullbackLift_eta {β₁ : H₁ →* H} {β₂ : H₂ →* H}
    {K : Type v} [Group K]
    (ψ : K →* FiberProduct.carrier β₁ β₂) :
    FiberProduct.lift β₁ β₂
      ((FiberProduct.fst β₁ β₂).comp ψ)
      ((FiberProduct.snd β₁ β₂).comp ψ)
      (fun k => by exact (ψ k).2) = ψ := by
  apply FiberProduct.hom_ext
  · intro k
    rfl
  · intro k
    rfl

/-- Symmetry of the concrete pullback.-/
def pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    FiberProduct.carrier β₁ β₂ ≃* FiberProduct.carrier β₂ β₁ where
  toFun := fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩
  invFun := fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  map_mul' := by
    intro x y
    apply Subtype.ext
    rfl

/-- The first projection after swapping equals the original second projection.-/
@[simp] theorem pullbackFst_pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (x : FiberProduct.carrier β₁ β₂) :
    FiberProduct.fst β₂ β₁ (pullbackSwap β₁ β₂ x) = FiberProduct.snd β₁ β₂ x :=
  rfl

/-- The second projection after swapping equals the original first projection.-/
@[simp] theorem pullbackSnd_pullbackSwap (β₁ : H₁ →* H) (β₂ : H₂ →* H)
    (x : FiberProduct.carrier β₁ β₂) :
    FiberProduct.snd β₂ β₁ (pullbackSwap β₁ β₂ x) = FiberProduct.fst β₁ β₂ x :=
  rfl

/--
The symmetry map for the algebraic pullback is inverse to the corresponding swapped pullback
comparison.-/
@[simp] theorem pullbackSwap_symm (β₁ : H₁ →* H) (β₂ : H₂ →* H) :
    (pullbackSwap β₁ β₂).symm = pullbackSwap β₂ β₁ :=
  rfl

end

end ProCGroups.Categorical
