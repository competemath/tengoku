/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Properties of C⋆-algebra homomorphisms

Here we collect properties of C⋆-algebra homomorphisms.

## Main declarations

+ `NonUnitalStarAlgHom.norm_map`: A non-unital star algebra monomorphism of complex C⋆-algebras
  is isometric.
-/

public section

open CStarAlgebra

open ContinuousFunctionalCalculus in
/--
@isnad1 id=eq.2h7v.s8.a14b4682131f from=seed src=0 shape=a3bf29e8 vocab=4502c6d9
-/
lemma IsSelfAdjoint.map_spectrum_real {F 𝕜 A B : Type*} [RCLike 𝕜]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A] [Algebra 𝕜 A]
    [Ring B] [StarRing B] [TopologicalSpace B] [Algebra ℝ B] [Algebra 𝕜 B]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
    [IsScalarTower ℝ 𝕜 A] [IsScalarTower ℝ 𝕜 B]
    [ContinuousMap.UniqueHom ℝ B] [FunLike F A B] [AlgHomClass F 𝕜 A B] [StarHomClass F A B]
    {a : A} (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ)
    (hφ' : Continuous φ := by fun_prop) :
    spectrum ℝ (φ a) = spectrum ℝ a := by
  have h_spec := AlgHom.spectrum_apply_subset ((φ : A →⋆ₐ[𝕜] B).restrictScalars ℝ) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx ↦ ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's lemma we can get a function for which `f x = 1`, but
  `f = 0` on `spectrum ℝ a`. -/
  by_contra hx'
  obtain ⟨f, h_eqOn, h_eqOn_x, -⟩ := exists_continuous_zero_one_of_isClosed
    (isCompact_spectrum (R := ℝ) (φ a)).isClosed (isClosed_singleton (x := x)) <| by simpa
  /- it suffices to show that `φ (f a) = 0`, for if so, then `f a = 0` by injectivity of `φ`, and
  hence `f = 0` on `spectrum ℝ a`, contradicting the fact that `f x = 1`. -/
  suffices φ (cfc f a) = 0 by
    rw [map_eq_zero_iff φ hφ, ← cfc_zero ℝ a, cfc_eq_cfc_iff_eqOn] at this
    exact zero_ne_one <| calc
      0 = f x := (this hx).symm
      _ = 1 := h_eqOn_x <| Set.mem_singleton x
  /- Finally, `φ (f a) = f (φ a) = 0`, where the last equality follows since `f = 0` on
  `spectrum ℝ (φ a)`. -/
  calc φ (cfc f a) = cfc f (φ a) := StarAlgHomClass.map_cfc φ f a
    _ = cfc (0 : ℝ → ℝ) (φ a) := cfc_congr h_eqOn
    _ = 0 := by simp

open CStarAlgebra in
/--
@isnad1 id=eq.2h5v.s8.5782bfc867f2 from=seed src=0 shape=bffcce67 vocab=fb982a8f
-/
lemma IsSelfAdjoint.map_quasispectrum_real {F A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    {a : A} (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ) :
    quasispectrum ℝ (φ a) = quasispectrum ℝ a := by
  replace hφ : Function.Injective (φ : A →⋆ₙₐ[ℂ] B) := hφ
  simpa [Unitization.starMap_inr, ← Unitization.quasispectrum_eq_spectrum_inr']
    using (ha.inr ℂ).map_spectrum_real _ (Unitization.starMap_injective hφ)

section OrderEmbedding

variable {F A B : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- A non-unital star monomorphism between C⋆-algebras is an order embedding. -/
def NonUnitalStarAlgHom.toOrderEmbedding (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) :
    A ↪o B where
  toFun := φ
  inj' := hφ
  map_rel_iff' {a b} := by
    simp only [Function.Embedding.coeFn_mk]
    refine ⟨?_, (OrderHomClass.mono φ ·)⟩
    rw [← sub_nonneg, ← sub_nonneg (a := b), ← map_sub φ]
    simp_rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, QuasispectrumRestricts.nnreal_iff]
    rintro ⟨h₁, h₂⟩
    have h_sa := h₁.of_map φ hφ
    exact ⟨h_sa, by rwa [← h_sa.map_quasispectrum_real φ hφ]⟩

/-- A non-unital star monomorphism between C⋆-algebras is an order embedding.
@isnad1 id=iff.1h6v.s8.600154f6a670 from=seed src=0 shape=52d9d107 vocab=361a4dc0
-/
protected lemma NonUnitalStarAlgHom.map_le_map_iff (f : F) (hf : Function.Injective f) {x y : A} :
    f x ≤ f y ↔ x ≤ y :=
  (toOrderEmbedding (f : A →⋆ₙₐ[ℂ] B) hf).le_iff_le

/--
@isnad1 id=iff.1h6v.s8.385447f9987c from=seed src=0 shape=52d9d107 vocab=44a04bc9
-/
protected lemma NonUnitalStarAlgHom.map_lt_map_iff (f : F) (hf : Function.Injective f) {x y : A} :
    f x < f y ↔ x < y :=
  (toOrderEmbedding (f : A →⋆ₙₐ[ℂ] B) hf).lt_iff_lt

end OrderEmbedding
namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open CStarAlgebra Unitization in
/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric.
@isnad1 id=eq.1h5v.s7.cf80aa9721a9 from=seed src=0 shape=689c6513 vocab=bf85b728
-/
lemma norm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖ = ‖a‖ := by
  /- Since passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices ∀ {ψ : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B} (_ : Function.Injective ψ)
      (a : Unitization ℂ A), ‖ψ a‖ = ‖a‖ by
    simpa [norm_inr] using this (starMap_injective (φ := (φ : A →⋆ₙₐ[ℂ] B)) hφ) a
  intro ψ hψ a
  -- to show `‖ψ a‖ = ‖a‖`, by the C⋆-property it suffices to show `‖ψ (star a * a)‖ = ‖star a * a‖`
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp only [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
  /- since `star a * a` is selfadjoint, it has the same `ℝ`-spectrum as `ψ (star a * a)`.
  Since the spectral radius over `ℝ` coincides with the norm, `‖ψ (star a * a)‖ = ‖star a * a‖`. -/
  have ha : IsSelfAdjoint (star a * a) := .star_mul_self a
  calc ‖ψ (star a * a)‖ = (spectralRadius ℝ (ψ (star a * a))).toReal :=
      ha.map ψ |>.toReal_spectralRadius_eq_norm.symm
    _ = (spectralRadius ℝ (star a * a)).toReal := by
      simp only [spectralRadius, ha.map_spectrum_real ψ hψ]
    _ = ‖star a * a‖ := ha.toReal_spectralRadius_eq_norm

/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric.
@isnad1 id=eq.1h5v.s7.a53b83d90c3a from=seed src=0 shape=689c6513 vocab=e496e0a6
-/
lemma nnnorm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_map φ hφ a

/--
@isnad1 id=isometry.1h4v.s7.779808a66707 from=seed src=0 shape=bcf2ce3b vocab=65359fc5
-/
lemma isometry (φ : F) (hφ : Function.Injective φ) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

end NonUnitalStarAlgHom
