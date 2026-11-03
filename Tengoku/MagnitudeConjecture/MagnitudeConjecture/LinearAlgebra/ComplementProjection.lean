import Tengoku.Seed.LinearAlgebra.Projection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A linear complement identity -/

set_option autoImplicit false

namespace MagnitudeConjecture

universe u₁ u₂ u₃ u₄

/-- Subtracting a component annihilated by a linear map does not change
the image.
@isnad1 id=eq.1h8v.s9.03484c5267bf from=translated src=- shape=757092e8 vocab=6cdea331
-/
theorem linearMap_sub_comp_apply_eq
    {R : Type u₁} {J : Type u₂} {B : Type u₃} {K : Type u₄}
    [Ring R]
    [AddCommGroup J] [Module R J]
    [AddCommGroup B] [Module R B]
    [AddCommGroup K] [Module R K]
    (g : J →ₗ[R] K) (i : B →ₗ[R] J) (p : J →ₗ[R] B)
    (h : LinearMap.ker g = LinearMap.range i) (z : J) :
    g (((LinearMap.id : J →ₗ[R] J) - i.comp p) z) = g z := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  change g z - g (i (p z)) = g z
  have hi : g (i (p z)) = 0 := by
    rw [← LinearMap.mem_ker, h]
    exact LinearMap.mem_range_self i (p z)
  rw [hi, sub_zero]

/-- The complementary projection `id - i p` has zero `p`-coordinate when
`p i = id`.
@isnad1 id=eq.1h6v.s8.d4e6c4d67ea3 from=translated src=- shape=05e92d91 vocab=8a72bff2
-/
theorem linearMap_projection_sub_comp_apply_eq_zero
    {R : Type u₁} {J : Type u₂} {B : Type u₃}
    [Ring R]
    [AddCommGroup J] [Module R J]
    [AddCommGroup B] [Module R B]
    (i : B →ₗ[R] J) (p : J →ₗ[R] B)
    (h : p.comp i = LinearMap.id) (z : J) :
    p (((LinearMap.id : J →ₗ[R] J) - i.comp p) z) = 0 := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  have hpi : p (i (p z)) = p z := by
    have hz := LinearMap.congr_fun h (p z)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hz
  change p z - p (i (p z)) = 0
  rw [hpi, sub_self]

/-- If the kernel of `g` is the range of a split inclusion `i`, then the
complementary projection `id - i p` kills the kernel of `g`.
@isnad1 id=le.2h7v.s9.6eaed1bdab98 from=translated src=- shape=329d4e39 vocab=01400ef4
-/
theorem linearMap_ker_le_ker_sub_comp
    {R : Type u₁} {J : Type u₂} {B : Type u₃} {K : Type u₄}
    [Ring R]
    [AddCommGroup J] [Module R J]
    [AddCommGroup B] [Module R B]
    [AddCommGroup K] [Module R K]
    (g : J →ₗ[R] K) (i : B →ₗ[R] J) (p : J →ₗ[R] B)
    (hker : LinearMap.ker g = LinearMap.range i)
    (hret : p.comp i = LinearMap.id) :
    LinearMap.ker g ≤
      LinearMap.ker ((LinearMap.id : J →ₗ[R] J) - i.comp p) := by
  rw [hker]
  rintro z ⟨u, rfl⟩
  rw [LinearMap.mem_ker]
  change i u - i (p (i u)) = 0
  have hu := LinearMap.congr_fun hret u
  rw [LinearMap.comp_apply, LinearMap.id_apply] at hu
  rw [hu, sub_self]

end MagnitudeConjecture
