/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
 # is_proj'

This file contains the definition of `linear_map.is_proj'` and lemmas relating to it, which is
essentially `linear_map.is_proj` but as a linear map from `E` to `U`.
-/

@[expose] public section

section

variable {R E : Type _} [Ring R] [AddCommGroup E] [Module R E] {U : Submodule R E}

/-- `linear_map.is_proj` but as a linear map from `E` to `U`. -/
def isProj' {p : E →ₗ[R] E} (hp : LinearMap.IsProj U p) : E →ₗ[R] U
    where
  toFun x := ⟨p x, hp.1 x⟩
  map_add' x y := by simp_rw [map_add, AddMemClass.mk_add_mk]
  map_smul' r x := by simp_rw [LinearMap.map_smul, RingHom.id_apply, SetLike.mk_smul_mk]

/--
@isnad1 id=eq.1h5v.s8.0cf523635bf2 from=translated src=- shape=5f54cf0e vocab=4156cfe1
-/
theorem isProj'_apply {p : E →ₗ[R] E} (hp : LinearMap.IsProj U p) (x : E) : ↑(isProj' hp x) = p x :=
  rfl

/--
@isnad1 id=eq.1h5v.s8.83cf3291d48a from=translated src=- shape=b5956709 vocab=4156cfe1
-/
theorem isProj'_eq {p : E →ₗ[R] E} (hp : LinearMap.IsProj U p) : ∀ x : U, isProj' hp (x : E) = x :=
  by
  intro x
  ext
  simp_rw [isProj'_apply, LinearMap.IsProj.map_id hp _ (SetLike.coe_mem x)]

end

variable {E 𝕜 : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/--
@isnad1 id=eq.0h3v.s9.1835c7d66d67 from=translated src=- shape=5f1bdd9a vocab=6d74ce6d
-/
theorem orthogonalProjection_eq_linear_proj' {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] :
    (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) =
      Submodule.projectionOnto K _ K.isCompl_orthogonal :=
  Submodule.toLinearMap_orthogonalProjectionOnto_eq_projectionOnto

/--
@isnad1 id=eq.0h4v.s10.d68dfdb5c569 from=translated src=- shape=a5574e61 vocab=79c67dad
-/
theorem orthogonalProjection_eq_linear_proj''
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (x : E) :
    K.orthogonalProjectionOnto x =
      Submodule.projectionOnto K _ K.isCompl_orthogonal x :=
  Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto x

/-- The orthogonal projection onto a submodule as an endomorphism of the ambient space. -/
noncomputable def orthogonalProjection'
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.starProjection

/--
@isnad1 id=eq.0h4v.s10.ade3e2c25f50 from=translated src=- shape=08b1abcc vocab=768acd8c
-/
theorem orthogonalProjection'_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (x : E) :
    orthogonalProjection' U x = U.orthogonalProjectionOnto x :=
  rfl

local notation "P" => Submodule.orthogonalProjectionOnto

local notation "↥P" => orthogonalProjection'

namespace orthogonalProjection

/--
@isnad1 id=eq.0h3v.s8.829376eb248c from=translated src=- shape=9decdfee vocab=3795ffe0
-/
theorem range (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (↥P U).range = U :=
  Submodule.range_starProjection U

end orthogonalProjection

/--
@isnad1 id=eq.0h3v.s9.887c7b909958 from=translated src=- shape=dbbe7727 vocab=c5f62f75
-/
@[simp]
theorem orthogonalProjection'_eq (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    ↥P U = U.subtypeL.comp (P U) :=
  rfl

/--
@isnad1 id=eq.0h3v.s10.e06a3d2044f8 from=translated src=- shape=c81be898 vocab=aaa846cf
-/
theorem orthogonal_projection'_eq_linear_proj {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] :
    (K.subtypeL.comp K.orthogonalProjectionOnto : E →ₗ[𝕜] E) =
      (K.subtype).comp
        (K.projectionOnto Kᗮ K.isCompl_orthogonal) :=
  by simpa [Submodule.starProjection, Submodule.projection] using
    Submodule.toLinearMap_starProjection_eq_isComplProjection (K := K)

/--
@isnad1 id=eq.0h4v.s10.dde141da9252 from=translated src=- shape=3e81d4e0 vocab=8c227d70
-/
theorem orthogonalProjection'_eq_linear_proj'
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (x : E) :
    (orthogonalProjection' K : E →ₗ[𝕜] E) x =
      (K.subtype).comp
        (K.projectionOnto Kᗮ K.isCompl_orthogonal) x := by
  rw [← orthogonal_projection'_eq_linear_proj]
  rfl
