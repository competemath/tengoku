/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.NormalBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonzero character eigenvectors from a normal basis

An inverse-character weighted sum of the normal basis transforms by the
character. Its coordinate at the identity automorphism is one, so the sum
is nonzero, without any assumption on the characteristic or group order.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

open scoped BigOperators

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The inverse-character weighted sum of the canonical normal basis.-/
def normalBasisCharacterEigenvector (χ : (L ≃ₐ[K] L) →* Kˣ) : L :=
  ∑ δ : L ≃ₐ[K] L, (((χ δ)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L δ

/-- Left translation of the normal basis gives the prescribed character action.
@isnad1 id=eq.0h4v.s9.28eed37689df from=translated src=- shape=0ebc2cb3 vocab=12ef07e9
-/
theorem normalBasisCharacterEigenvector_eigen (χ : (L ≃ₐ[K] L) →* Kˣ)
    (σ : L ≃ₐ[K] L) :
    σ (normalBasisCharacterEigenvector χ) =
      (χ σ : K) • normalBasisCharacterEigenvector χ := by
  classical
  unfold normalBasisCharacterEigenvector
  calc
    σ (∑ δ : L ≃ₐ[K] L, (((χ δ)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L δ) =
        ∑ δ : L ≃ₐ[K] L,
          (((χ δ)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L (σ * δ) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro δ hδ
      rw [map_smul, IsGalois.normalBasis_apply δ,
        IsGalois.normalBasis_apply (σ * δ), AlgEquiv.mul_apply]
    _ = ∑ δ : L ≃ₐ[K] L,
        (χ σ : K) • ((((χ (σ * δ))⁻¹ : Kˣ) : K) •
          IsGalois.normalBasis K L (σ * δ)) := by
      apply Finset.sum_congr rfl
      intro δ hδ
      rw [smul_smul, χ.map_mul σ δ, mul_inv_rev, Units.val_mul,
        mul_left_comm (χ σ : K), Units.mul_inv, mul_one]
    _ = ∑ δ : L ≃ₐ[K] L,
        (χ σ : K) • ((((χ δ)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L δ) :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective σ)
        (fun δ : L ≃ₐ[K] L =>
          (χ σ : K) • ((((χ δ)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L δ))
    _ = (χ σ : K) •
        ∑ δ : L ≃ₐ[K] L, (((χ δ)⁻¹ : Kˣ) : K) • IsGalois.normalBasis K L δ :=
      Finset.smul_sum.symm

/-- The identity coordinate of the weighted sum is one.
@isnad1 id=ne.0h3v.s8.b44045f70c67 from=translated src=- shape=e0b086f9 vocab=63d91bdd
-/
theorem normalBasisCharacterEigenvector_ne_zero (χ : (L ≃ₐ[K] L) →* Kˣ) :
    normalBasisCharacterEigenvector χ ≠ 0 := by
  classical
  have hcoord : (IsGalois.normalBasis K L).repr
      (normalBasisCharacterEigenvector χ) 1 = (1 : K) := by
    have h := congrFun ((IsGalois.normalBasis K L).repr_sum_self
      (fun δ : L ≃ₐ[K] L => (((χ δ)⁻¹ : Kˣ) : K))) 1
    simpa only [normalBasisCharacterEigenvector, map_one, inv_one, Units.val_one] using h
  intro hzero
  rw [hzero, map_zero, Finsupp.zero_apply] at hcoord
  exact zero_ne_one hcoord

/-- Every base-field-valued character of a finite Galois group occurs in the field.
@isnad1 id=ex.0h3v.s9.b43e0fe9f656 from=translated src=- shape=d13ec390 vocab=0a6c42e2
-/
theorem exists_nonzero_characterEigenvector (χ : (L ≃ₐ[K] L) →* Kˣ) :
    ∃ b : L, b ≠ 0 ∧ ∀ σ : L ≃ₐ[K] L, σ b = (χ σ : K) • b :=
  ⟨normalBasisCharacterEigenvector χ, normalBasisCharacterEigenvector_ne_zero χ,
    normalBasisCharacterEigenvector_eigen χ⟩

end LocalFieldTheory.DiscreteValuationField
