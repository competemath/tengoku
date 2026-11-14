/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import Tengoku.Seed.FieldTheory.Galois.NormalBasis
import Tengoku.Seed.GroupTheory.GroupAction.Defs
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.RingTheory.Norm.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Ideles in finite extensions: the tensor-product model

This file uses the canonical presentation
`𝔸_L = 𝔸_K ⊗_K L`.  This makes extension, Galois conjugation, and the
idele norm formal linear-algebra operations.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The adele algebra of `L`, written in base-change form
`𝔸_K ⊗_K L`.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.RelativeAdeleRing :=
  NumberField.AdeleRing (𝓞 K) K ⊗[K] L

/-- The idele group of the base-changed adele algebra.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup :=
  (RelativeAdeleRing K L)ˣ

namespace Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup

/--
@isnad1 id=nontrivi.0h1v.s4.3a66de080b6c from=translated src=- shape=5a2b787c vocab=eedd0616
-/
instance baseAdeleRingNontrivial :
    Nontrivial (NumberField.AdeleRing (𝓞 K) K) :=
  Function.Injective.nontrivial
    (NumberField.AdeleRing.algebraMap_injective
      (R := 𝓞 K) (K := K))

/-- The base-adele algebra map into its scalar extension.-/
def adeleInclusion :
    NumberField.AdeleRing (𝓞 K) K →+*
      RelativeAdeleRing K L :=
  (Algebra.TensorProduct.includeLeft
    (R := K) (S := K)
    (A := NumberField.AdeleRing (𝓞 K) K) (B := L)).toRingHom

/-- The extension field embedded in the scalar-extended adele algebra.-/
def fieldInclusion :
    L →+* RelativeAdeleRing K L :=
  (Algebra.TensorProduct.includeRight
    (R := K) (A := NumberField.AdeleRing (𝓞 K) K)
    (B := L)).toRingHom

/-- The canonical inclusion `I_K → I_L` in the tensor-product model.-/
def inclusion :
    IdeleGroup K →* RelativeIdeleGroup K L :=
  (Units.map (adeleInclusion K L)).comp
    (IdeleGroup.equivAdeleRingUnits (K := K)).toMonoidHom

omit [NumberField L] in
/--
@isnad1 id=injectiv.0h2v.s11.b86c951bded6 from=translated src=- shape=afbc5f55 vocab=8131881b
-/
theorem inclusion_injective :
    Function.Injective (inclusion K L) := by
  exact
    (Units.map_injective
      (Algebra.TensorProduct.includeLeft_injective
        (R := K) (S := K)
        (A := NumberField.AdeleRing (𝓞 K) K) (B := L)
        (FaithfulSMul.algebraMap_injective K L))).comp
      (IdeleGroup.equivAdeleRingUnits (K := K)).injective

/-- The diagonal copy of `Lˣ` inside the relative idele group.-/
def principalIdele :
    Lˣ →* RelativeIdeleGroup K L :=
  Units.map (fieldInclusion K L)

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h3v.s12.97a47f07ee9d from=translated src=- shape=70f415ce vocab=5bd224dd
-/
@[simp]
theorem inclusion_principalIdele
    (x : Kˣ) :
    inclusion K L (IdeleGroup.principalIdele K x) =
      principalIdele K L
        (Units.map (algebraMap K L) x) := by
  apply Units.ext
  change
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := L))
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) (x : K)) =
      (Algebra.TensorProduct.includeRight
        (R := K) (A := NumberField.AdeleRing (𝓞 K) K)
        (B := L))
        (algebraMap K L (x : K))
  simp

/-- The norm of relative ideles, obtained as the determinant over
the base adele ring.-/
def norm :
    RelativeIdeleGroup K L →* IdeleGroup K :=
  (IdeleGroup.equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map
      (Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)))

omit [NumberField L] in
/--
@isnad1 id=eq.0h3v.s12.5c53742022c2 from=translated src=- shape=1ed93046 vocab=57349bb1
-/
@[simp]
theorem norm_inclusion (a : IdeleGroup K) :
    norm K L (inclusion K L a) =
      a ^ Module.finrank K L := by
  apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  simp only [norm, inclusion, MonoidHom.comp_apply]
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (algebraMap
          (NumberField.AdeleRing (𝓞 K) K)
          (RelativeAdeleRing K L)
          ((IdeleGroup.equivAdeleRingUnits (K := K) a :
            (NumberField.AdeleRing (𝓞 K) K)ˣ) :
            NumberField.AdeleRing (𝓞 K) K)) =
      (((IdeleGroup.equivAdeleRingUnits (K := K) a) ^
          Module.finrank K L :
        (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K)
  rw [Algebra.norm_algebraMap,
    Module.finrank_baseChange]
  rfl

omit [NumberField L] in
/-- Norm commutes with scalar extension from `K` to the base adele ring.
@isnad1 id=eq.0h3v.s10.654354429390 from=translated src=- shape=4082bd25 vocab=438199df
-/
theorem norm_fieldInclusion (x : L) :
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L x) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange
    (NumberField.AdeleRing (𝓞 K) K)
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b,
    (algebraMap K
      (NumberField.AdeleRing (𝓞 K) K)).map_det]
  congr 1
  ext i j
  simp [bA, b, fieldInclusion,
    Algebra.smul_def,
    Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField L] in
/-- The relative idele norm carries a principal idele to the
principal idele of the field norm.
@isnad1 id=eq.0h3v.s12.48974314c86e from=translated src=- shape=dd9d846a vocab=97ef5118
-/
@[simp]
theorem norm_principalIdele (x : Lˣ) :
    norm K L (principalIdele K L x) =
      IdeleGroup.principalIdele K
        (Units.map (Algebra.norm K) x) := by
  apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L (x : L)) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K (x : L))
  exact norm_fieldInclusion K L (x : L)

/-- Galois conjugation on the scalar-extended adele algebra.-/
def conjugation
    (σ : L ≃ₐ[K] L) :
    RelativeAdeleRing K L ≃ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K L :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h5v.s10.ad79e62caf93 from=translated src=- shape=288e0bc8 vocab=46003a14
-/
@[simp]
theorem conjugation_tmul
    (σ : L ≃ₐ[K] L)
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    conjugation K L σ (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x := by
  rfl

/-- Galois conjugation on relative ideles.-/
def conjugationIdele
    (σ : L ≃ₐ[K] L) :
    RelativeIdeleGroup K L ≃*
      RelativeIdeleGroup K L :=
  Units.mapEquiv (conjugation K L σ).toMulEquiv

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s11.f37016ec96df from=translated src=- shape=ac9ad28d vocab=c84b7771
-/
@[simp]
theorem conjugationIdele_coe
    (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    ((conjugationIdele K L σ a :
      RelativeIdeleGroup K L) : RelativeAdeleRing K L) =
      conjugation K L σ (a : RelativeAdeleRing K L) :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h3v.s10.abcf1743844e from=translated src=- shape=04a5f3f9 vocab=6bdd8efd
-/
theorem conjugation_one
    (a : RelativeAdeleRing K L) :
    conjugation K L (1 : L ≃ₐ[K] L) a = a := by
  change
    Algebra.TensorProduct.congr
        (AlgEquiv.refl :
          NumberField.AdeleRing (𝓞 K) K ≃ₐ[
            NumberField.AdeleRing (𝓞 K) K]
            NumberField.AdeleRing (𝓞 K) K)
        (AlgEquiv.refl : L ≃ₐ[K] L) a =
      a
  rw [Algebra.TensorProduct.congr_refl]
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h5v.s11.9c702d7257b9 from=translated src=- shape=a82f459c vocab=1746847e
-/
theorem conjugation_mul
    (σ τ : L ≃ₐ[K] L)
    (a : RelativeAdeleRing K L) :
    conjugation K L (σ * τ) a =
      conjugation K L σ (conjugation K L τ a) := by
  let e :
      NumberField.AdeleRing (𝓞 K) K ≃ₐ[
        NumberField.AdeleRing (𝓞 K) K]
        NumberField.AdeleRing (𝓞 K) K :=
    AlgEquiv.refl
  have he : e.trans e = e := by
    ext
    rfl
  have h :=
    Algebra.TensorProduct.congr_trans e e τ σ
  rw [he] at h
  change
    Algebra.TensorProduct.congr e (τ.trans σ) a =
      Algebra.TensorProduct.congr e σ
        (Algebra.TensorProduct.congr e τ a)
  exact congrArg
    (fun f :
      RelativeAdeleRing K L ≃ₐ[
        NumberField.AdeleRing (𝓞 K) K]
        RelativeAdeleRing K L ↦ f a) h

/-- The natural Galois action on relative ideles.-/
instance relativeIdeleMulAction :
    MulAction (L ≃ₐ[K] L) (RelativeIdeleGroup K L) where
  smul σ a := conjugationIdele K L σ a
  one_smul a := by
    apply Units.ext
    exact conjugation_one K L (a : RelativeAdeleRing K L)
  mul_smul σ τ a := by
    apply Units.ext
    change conjugation K L (σ * τ)
        (a : RelativeAdeleRing K L) =
      conjugation K L σ
        (conjugation K L τ (a : RelativeAdeleRing K L))
    exact conjugation_mul K L σ τ _

/-- The natural Galois action on relative ideles, viewed as an action by
group automorphisms.-/
@[reducible]
noncomputable def relativeIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup K L) where
  __ := relativeIdeleMulAction K L
  smul_one σ := map_one (conjugationIdele K L σ)
  smul_mul σ a b := map_mul (conjugationIdele K L σ) a b

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s10.f99b18736570 from=translated src=- shape=7661cbb9 vocab=2f565dd5
-/
@[simp]
theorem smul_def
    (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    σ • a = conjugationIdele K L σ a :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s12.f291ddd88f4c from=translated src=- shape=b74a66db vocab=9cdb6c40
-/
@[simp]
theorem smul_inclusion
    (σ : L ≃ₐ[K] L) (a : IdeleGroup K) :
    σ • inclusion K L a = inclusion K L a := by
  apply Units.ext
  change conjugation K L σ
      (algebraMap
        (NumberField.AdeleRing (𝓞 K) K)
        (RelativeAdeleRing K L)
        ((IdeleGroup.equivAdeleRingUnits (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
          NumberField.AdeleRing (𝓞 K) K)) =
    algebraMap
      (NumberField.AdeleRing (𝓞 K) K)
      (RelativeAdeleRing K L)
      ((IdeleGroup.equivAdeleRingUnits (K := K) a :
        (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K)
  exact (conjugation K L σ).commutes _

omit [NumberField L] [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s10.ca76482e5735 from=translated src=- shape=f7d2d68f vocab=2f502b57
-/
@[simp]
theorem smul_principalIdele
    (σ : L ≃ₐ[K] L) (x : Lˣ) :
    σ • principalIdele K L x =
      principalIdele K L (Units.map σ.toRingEquiv.toMonoidHom x) := by
  apply Units.ext
  change conjugation K L σ
      (Algebra.TensorProduct.includeRight (x : L)) =
    Algebra.TensorProduct.includeRight (σ (x : L))
  change conjugation K L σ (1 ⊗ₜ[K] (x : L)) =
    1 ⊗ₜ[K] σ (x : L)
  rw [conjugation_tmul]

/-- Reynolds averaging for the finite Galois action.-/
def galoisAverage
    (z : RelativeAdeleRing K L) :
    RelativeAdeleRing K L :=
  ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹) •
    ∑ σ : L ≃ₐ[K] L, conjugation K L σ z

omit [NumberField L] in
/--
@isnad1 id=eq.1h3v.s10.17b60983639c from=translated src=- shape=9741e987 vocab=82e31411
-/
theorem galoisAverage_eq_of_fixed
    [IsGalois K L]
    (z : RelativeAdeleRing K L)
    (hz : ∀ σ : L ≃ₐ[K] L,
      conjugation K L σ z = z) :
    galoisAverage K L z = z := by
  rw [galoisAverage]
  simp_rw [hz]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul K, ← mul_smul,
    inv_mul_cancel₀
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    one_smul]

omit [NumberField L] in
/--
@isnad1 id=eq.0h4v.s10.cac8adb40291 from=translated src=- shape=6e9cb844 vocab=ac5fcf17
-/
theorem galoisAverage_tmul
    [IsGalois K L]
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    galoisAverage K L (a ⊗ₜ[K] x) =
      adeleInclusion K L
        (a * algebraMap K
          (NumberField.AdeleRing (𝓞 K) K)
          ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹ *
            Algebra.trace K L x)) := by
  rw [galoisAverage]
  simp_rw [conjugation_tmul]
  rw [← TensorProduct.tmul_sum,
    ← trace_eq_sum_automorphisms x]
  change
    ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹) •
        (a ⊗ₜ[K]
          algebraMap K L (Algebra.trace K L x)) =
      (a * algebraMap K
        (NumberField.AdeleRing (𝓞 K) K)
        ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹ *
          Algebra.trace K L x)) ⊗ₜ[K] 1
  rw [TensorProduct.smul_tmul',
    Algebra.algebraMap_eq_smul_one]
  rw [← TensorProduct.smul_tmul]
  congr 1
  simp [Algebra.smul_def, map_mul, mul_assoc, mul_comm]

/-- The subgroup of relative ideles fixed by every Galois automorphism.-/
def galoisFixedSubgroup :
    Subgroup (RelativeIdeleGroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact FixedPoints.subgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L)

end Tengoku.ClassfieldtheoryYamaguchi.RelativeIdeleGroup
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
