import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length

set_option autoImplicit false
set_option maxHeartbeats 800000

open IsLocalRing

namespace PrincipalQuotLength

section General
variable {R : Type*} [CommRing R]

noncomputable def mulQuot (x y : R) : (R ⧸ Ideal.span {y}) →ₗ[R] (R ⧸ Ideal.span {x * y}) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft R x) (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩)

/--
@isnad1 id=eq.0h4v.s10.8e0b32fd550b from=translated src=- shape=8e5d5f41 vocab=714f6cc7
-/
theorem mulQuot_mk (x y r : R) : mulQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) := rfl

noncomputable def projQuot (x y : R) : (R ⧸ Ideal.span {x * y}) →ₗ[R] (R ⧸ Ideal.span {x}) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)

/--
@isnad1 id=eq.0h4v.s10.0e30988c9c31 from=translated src=- shape=4d86d957 vocab=d6290bc0
-/
theorem projQuot_mk (x y r : R) : projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl

/--
@isnad1 id=surjecti.0h3v.s9.081a5574a89a from=translated src=- shape=e3d95418 vocab=1abe9154
-/
theorem projQuot_surjective (x y : R) : Function.Surjective (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

/--
@isnad1 id=injectiv.1h3v.s9.256ddcba54f6 from=translated src=- shape=c4b8289e vocab=fd602cb8
-/
theorem mulQuot_injective [IsDomain R] (x y : R) (hx : x ≠ 0) : Function.Injective (mulQuot x y) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [LinearMap.mem_ker, mulQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_singleton'.mpr ⟨s, mul_left_cancel₀ hx ?_⟩
  rw [← hs]; ring

/--
@isnad1 id=exact.0h3v.s10.a5dee735b68b from=translated src=- shape=1c4191a7 vocab=af1436c2
-/
theorem exact_mulQuot_projQuot (x y : R) : Function.Exact (mulQuot x y) (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [projQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuot_mk, mul_comm x c]⟩
  · rintro ⟨m', hm'⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
    rw [mulQuot_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm'
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm'
    refine Ideal.mem_span_singleton'.mpr ⟨r' - s * y, ?_⟩
    have : r = x * r' - s * (x * y) := by rw [hs]; ring
    rw [this]; ring

/--
@isnad1 id=eq.1h3v.s8.28667632880e from=translated src=- shape=bff9b24c vocab=07cdc118
-/
theorem length_quotient_mul [IsDomain R] (x y : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x * y}) =
      Module.length R (R ⧸ Ideal.span {y}) + Module.length R (R ⧸ Ideal.span {x}) :=
  Module.length_eq_add_of_exact (mulQuot x y) (projQuot x y) (mulQuot_injective x y hx) (projQuot_surjective x y)
    (exact_mulQuot_projQuot x y)

/--
@isnad1 id=eq.1h3v.s8.db81271ef312 from=translated src=- shape=b4d19c91 vocab=50c27b73
-/
theorem length_quotient_pow [IsDomain R] (x : R) (hx : x ≠ 0) (m : ℕ) :
    Module.length R (R ⧸ Ideal.span {x ^ m}) = m * Module.length R (R ⧸ Ideal.span {x}) := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, Module.length_eq_zero_iff, Ideal.span_singleton_one]
    infer_instance
  | succ m ih =>
    rw [pow_succ', length_quotient_mul x _ hx, ih, Nat.cast_succ]
    ring

/--
@isnad1 id=eq.1h3v.s8.6245ee68ef4b from=translated src=- shape=aa315af3 vocab=c18d5743
-/
theorem length_quotient_unit_mul {a : R} (ha : IsUnit a) (x : R) :
    Module.length R (R ⧸ Ideal.span {a * x}) = Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_mul_left_unit ha]

end General

end PrincipalQuotLength

open PrincipalQuotLength in
open IsDiscreteValuationRing in

/--
@isnad1 id=eq.2h4v.s9.bedfd0fc153f from=translated src=- shape=a5036fb0 vocab=2f775604
-/
theorem solution
    {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CommRing L] [IsDomain L] [IsLocalRing L]
    (φ : D →+* L) (hφ0 : Function.Injective φ)
    (f : D) (hf : f ≠ 0) :
    Module.length L (L ⧸ Ideal.span {φ f}) =
      Module.length D (D ⧸ Ideal.span {f}) * Module.length L (L ⧸ Ideal.map φ (IsLocalRing.maximalIdeal D)) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hmax : IsLocalRing.maximalIdeal D = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf ht
  have ht0 : t ≠ 0 := ht.ne_zero
  have hφt0 : φ t ≠ 0 := fun h => ht0 (hφ0 (by rw [h, map_zero]))

  have hD : Module.length D (D ⧸ Ideal.span {(u : D) * t ^ m}) = m := by
    rw [length_quotient_unit_mul u.isUnit, length_quotient_pow t ht0, ← hmax]
    have h1 : Module.length D (D ⧸ IsLocalRing.maximalIdeal D) = 1 :=
      Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
        ⟨IsLocalRing.maximalIdeal D, inferInstance, ⟨LinearEquiv.refl D (D ⧸ IsLocalRing.maximalIdeal D)⟩⟩)
    rw [h1, mul_one]

  have hL : Module.length L (L ⧸ Ideal.span {φ ((u : D) * t ^ m)}) = m * Module.length L (L ⧸ Ideal.span {φ t}) := by
    rw [map_mul, map_pow, length_quotient_unit_mul (u.isUnit.map φ), length_quotient_pow (φ t) hφt0]
  rw [hL, hD, hmax, Ideal.map_span, Set.image_singleton]
