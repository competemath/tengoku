/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
import Tengoku.Seed.FieldTheory.Normal.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Norms through an ambient Galois extension

This file proves the embedded-subextension determinant-norm formula.
If `L/K` is embedded in a finite Galois extension `M/K`, extending the
determinant norm of an element of `A ⊗[K] L` to `A ⊗[K] M` gives the
product over all `K`-embeddings `L → M`.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section

namespace Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup

universe u v w z

section EmbeddingsIntoGaloisExtension

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]

/-- Extend a `K`-embedding `L → M` to the algebraic closure of `M`.-/
def embeddingToAlgebraicClosure :
    (L →ₐ[K] M) →
      (L →ₐ[K] AlgebraicClosure M) :=
  fun f =>
    (IsScalarTower.toAlgHom K M
      (AlgebraicClosure M)).comp f

omit [Algebra L M] [IsScalarTower K L M] in
/--
@isnad1 id=injectiv.0h3v.s6.aa37e8170575 from=translated src=- shape=eb6fa97b vocab=4d2de544
-/
theorem embeddingToAlgebraicClosure_injective :
    Function.Injective
      (embeddingToAlgebraicClosure
        (K := K) (L := L) (M := M)) := by
  intro f g h
  ext x
  exact
    (algebraMap M (AlgebraicClosure M)).injective
      (DFunLike.congr_fun h x)

/--
@isnad1 id=surjecti.0h3v.s7.b3df47897dea from=translated src=- shape=38348be6 vocab=493d9384
-/
theorem embeddingToAlgebraicClosure_surjective
    [FiniteDimensional K M] [Normal K M] :
    Function.Surjective
      (embeddingToAlgebraicClosure
        (K := K) (L := L) (M := M)) := by
  intro f
  let C := AlgebraicClosure M
  let e : C →ₐ[K] C := f.liftNormal C
  let r : M →ₐ[K] M := e.restrictNormal M
  let j : L →ₐ[K] M :=
    IsScalarTower.toAlgHom K L M
  refine ⟨r.comp j, ?_⟩
  ext x
  change algebraMap M C
      (r (algebraMap L M x)) = f x
  rw [AlgHom.restrictNormal_commutes]
  change e (algebraMap L C x) = f x
  exact f.liftNormal_commutes C x

/-- Embeddings of a subextension into a finite normal overfield are the
same as embeddings into an algebraic closure.-/
noncomputable def embeddingToAlgebraicClosureEquiv
    [FiniteDimensional K M] [Normal K M] :
    (L →ₐ[K] M) ≃
      (L →ₐ[K] AlgebraicClosure M) :=
  Equiv.ofBijective embeddingToAlgebraicClosure
    ⟨embeddingToAlgebraicClosure_injective,
      embeddingToAlgebraicClosure_surjective⟩

/-- The subgroup of `Gal(M/K)` fixing the embedded copy of `L`.-/
def fixingSubextension :
    Subgroup (M ≃ₐ[K] M) :=
  (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup

/-- Restriction of an automorphism of `M/K` to the embedded copy of `L`.-/
def restrictToSubextension
    (σ : M ≃ₐ[K] M) : L →ₐ[K] M :=
  σ.toAlgHom.comp
    (IsScalarTower.toAlgHom K L M)

/-- Extend an embedding `L →ₐ[K] M` to an automorphism of the normal
extension `M/K`.-/
noncomputable def liftSubextensionEmbedding
    [Normal K M] (f : L →ₐ[K] M) :
    M ≃ₐ[K] M :=
  AlgEquiv.ofBijective (f.liftNormal M)
    (AlgHom.normal_bijective K M M _)

/--
@isnad1 id=eq.0h4v.s7.a292878afc82 from=translated src=- shape=212a4ca9 vocab=64df6d3b
-/
theorem restrict_liftSubextensionEmbedding
    [Normal K M] (f : L →ₐ[K] M) :
    restrictToSubextension
        (liftSubextensionEmbedding f) = f := by
  ext x
  exact f.liftNormal_commutes M x

/-- The canonical map from right cosets of the fixing subgroup to
embeddings of the subextension.-/
noncomputable def cosetToEmbedding
    [Normal K M] :
    (M ≃ₐ[K] M) ⧸
        fixingSubextension (K := K) (L := L) (M := M) →
      (L →ₐ[K] M) :=
  fun q ↦
    Quotient.liftOn' q restrictToSubextension (by
      intro σ τ hστ
      rw [QuotientGroup.leftRel_apply] at hστ
      ext x
      have hfix :=
        (IntermediateField.mem_fixingSubgroup_iff
          (IsScalarTower.toAlgHom K L M).fieldRange
          (σ⁻¹ * τ)).1 hστ
          (algebraMap L M x)
          (by exact ⟨x, rfl⟩)
      change σ (algebraMap L M x) =
        τ (algebraMap L M x)
      have ht : τ = σ * (σ⁻¹ * τ) := by
        group
      rw [ht, AlgEquiv.mul_apply, hfix])

/-- Right cosets `Gal(M/K)/Gal(M/L)` are canonically the `K`-embeddings
`L → M`. This is the index set in the coset form of the Galois product norm formula.-/
noncomputable def cosetEquivEmbedding
    [Normal K M] :
    (M ≃ₐ[K] M) ⧸
        fixingSubextension (K := K) (L := L) (M := M) ≃
      (L →ₐ[K] M) where
  toFun := cosetToEmbedding
  invFun f :=
    (liftSubextensionEmbedding f :
      (M ≃ₐ[K] M) ⧸
        fixingSubextension
          (K := K) (L := L) (M := M))
  right_inv f :=
    restrict_liftSubextensionEmbedding f
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro σ
    apply QuotientGroup.eq.mpr
    change
      (liftSubextensionEmbedding
          (restrictToSubextension σ))⁻¹ * σ ∈
        (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff
      (IsScalarTower.toAlgHom K L M).fieldRange]
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change
      ((liftSubextensionEmbedding
          (restrictToSubextension σ))⁻¹ * σ)
          (algebraMap L M x) =
        algebraMap L M x
    rw [AlgEquiv.mul_apply]
    have hres :=
      DFunLike.congr_fun
        (restrict_liftSubextensionEmbedding
          (restrictToSubextension σ)) x
    change
      liftSubextensionEmbedding
          (restrictToSubextension σ)
          (algebraMap L M x) =
        σ (algebraMap L M x) at hres
    rw [← hres]
    exact
      (liftSubextensionEmbedding
        (restrictToSubextension σ)).symm_apply_apply
          (algebraMap L M x)

/-- The field norm of a subextension, computed in an ambient finite
Galois extension, is the product over all embeddings into that extension.
@isnad1 id=eq.0h4v.s8.ca403606c71c from=translated src=- shape=d93a5cf3 vocab=4bedbb57
-/
theorem norm_eq_prod_embeddings_in_galoisExtension
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] (x : L) :
    algebraMap K M (Algebra.norm K x) =
      ∏ f : L →ₐ[K] M, f x := by
  let : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  apply
    (algebraMap M
      (AlgebraicClosure M)).injective
  rw [map_prod]
  calc
    algebraMap M (AlgebraicClosure M)
        (algebraMap K M (Algebra.norm K x)) =
      algebraMap K (AlgebraicClosure M)
        (Algebra.norm K x) := by
          rw [IsScalarTower.algebraMap_apply
            K M (AlgebraicClosure M)]
    _ = ∏ f : L →ₐ[K] AlgebraicClosure M, f x :=
      Algebra.norm_eq_prod_embeddings K
        (AlgebraicClosure M) x
    _ = ∏ f : L →ₐ[K] M,
        algebraMap M (AlgebraicClosure M) (f x) := by
      exact ((embeddingToAlgebraicClosureEquiv
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ f x)).symm

end EmbeddingsIntoGaloisExtension

section UniversalPolynomial

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

local instance :
    Fintype
      ((M ≃ₐ[K] M) ⧸
        fixingSubextension
          (K := K) (L := L) (M := M)) :=
  Fintype.ofFinite _

/-- The linear polynomial representing a chosen `K`-embedding `L → M`.-/
def embeddingPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M) :
    MvPolynomial ι M :=
  ∑ i, MvPolynomial.X i *
    MvPolynomial.C (f (b i))

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
/--
@isnad1 id=eq.0h7v.s9.781af6affd64 from=translated src=- shape=f635fe53 vocab=916540ed
-/
@[simp]
theorem eval_embeddingPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M)
    (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K M (b.repr x i))
        (embeddingPolynomial b f) =
      f x := by
  rw [embeddingPolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  calc
    ∑ i, algebraMap K M (b.repr x i) *
        f (b i) =
      ∑ i, f ((b.repr x i) • b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.smul_def]
    _ = f (∑ i, (b.repr x i) • b i) := by
      rw [map_sum]
    _ = f x := by rw [b.sum_repr]

/-- The universal product over all embeddings `L →ₐ[K] M`.-/
def embeddingProductPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial ι M :=
  ∏ f : L →ₐ[K] M, embeddingPolynomial b f

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [IsGalois K M] in
/--
@isnad1 id=eq.0h6v.s9.f98f6dd641c4 from=translated src=- shape=d3280b48 vocab=71944c41
-/
@[simp]
theorem eval_embeddingProductPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K M (b.repr x i))
        (embeddingProductPolynomial
          (M := M) b) =
      ∏ f : L →ₐ[K] M, f x := by
  simp [embeddingProductPolynomial]

/-- Scalar extension of an embedding `L → M` on tensor algebras.-/
def scalarEmbedding
    (A : Type*) [CommRing A] [Algebra K A]
    (f : L →ₐ[K] M) :
    A ⊗[K] L →ₐ[A] A ⊗[K] M :=
  Algebra.TensorProduct.map
    (AlgHom.id A A) f

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
/--
@isnad1 id=eq.0h7v.s9.e2c27d22d52b from=translated src=- shape=efa3704c vocab=3a4e12da
-/
@[simp]
theorem scalarEmbedding_tmul
    (A : Type*) [CommRing A] [Algebra K A]
    (f : L →ₐ[K] M) (a : A) (x : L) :
    scalarEmbedding A f (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] f x :=
  rfl

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
/-- Evaluation of an embedding polynomial after arbitrary scalar extension
is the corresponding tensor-algebra embedding.
@isnad1 id=eq.0h8v.s11.40feab593639 from=translated src=- shape=3bf1c329 vocab=26d0b7d8
-/
theorem eval₂_embeddingPolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A]
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M)
    (x : A ⊗[K] L) :
    MvPolynomial.eval₂
        ((Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := M)).toRingHom)
        (fun i ↦
          (Algebra.TensorProduct.includeLeft
            (R := K) (S := K) (A := A) (B := M))
            ((Algebra.TensorProduct.basis A b).repr x i))
        (embeddingPolynomial b f) =
      scalarEmbedding A f x := by
  simp only [embeddingPolynomial,
    MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C]
  calc
    ∑ i,
        (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := M))
          ((Algebra.TensorProduct.basis A b).repr x i) *
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := M))
          (f (b i)) =
      ∑ i, scalarEmbedding A f
        (((Algebra.TensorProduct.basis A b).repr x i) •
          Algebra.TensorProduct.basis A b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.TensorProduct.basis_apply,
          Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.smul_def]
    _ = scalarEmbedding A f
        (∑ i,
          ((Algebra.TensorProduct.basis A b).repr x i) •
            Algebra.TensorProduct.basis A b i) := by
      rw [map_sum]
    _ = scalarEmbedding A f x := by
      rw [(Algebra.TensorProduct.basis A b).sum_repr]

end UniversalPolynomial

section RelativeAdeles

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [NumberField K]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

local instance :
    Fintype
      ((M ≃ₐ[K] M) ⧸
        fixingSubextension
          (K := K) (L := L) (M := M)) :=
  Fintype.ofFinite _

/-- A field embedding inside an ambient Galois extension, extended to
relative adèles.-/
def adeleEmbedding (f : L →ₐ[K] M) :
    RelativeAdeleRing K L →ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K M :=
  scalarEmbedding
    (NumberField.AdeleRing (𝓞 K) K) f

/-- The induced homomorphism on relative idèles.-/
def ideleEmbedding (f : L →ₐ[K] M) :
    RelativeIdeleGroup K L →*
      RelativeIdeleGroup K M :=
  Units.map (adeleEmbedding f).toMonoidHom

end RelativeAdeles

end Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
