import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_free_quotient_range_of_ker_baseChange_residueField_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace P2mKcTorCrit

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
@isnad1 id=eq.0h4v.s10.0a0536559eee from=translated src=- shape=89c3f5ee vocab=df3a9f15
-/
theorem rangeRestrict_comp_ker_subtype (f : M →ₗ[R] N) :
    f.rangeRestrict.comp (LinearMap.ker f).subtype = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change f x = 0
  exact x.2

/--
@isnad1 id=eq.0h4v.s8.23f784871284 from=translated src=- shape=b7f39f7e vocab=eb4de2e2
-/
theorem subtype_comp_rangeRestrict (f : M →ₗ[R] N) :
    (LinearMap.range f).subtype.comp f.rangeRestrict = f :=
  LinearMap.ext fun _ => rfl

/--
@isnad1 id=injectiv.1h5v.s11.b81566e94f1b from=translated src=- shape=8dfcd8ba vocab=52a94cb7
-/
theorem lTensor_subtype_range_injective (A : Type*) [CommRing A] [Algebra R A] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange A) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange A)) :
    Function.Injective ((LinearMap.range f).subtype.lTensor A) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hsurj : Function.Surjective (f.rangeRestrict.lTensor A) :=
    LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict f)
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ LinearMap.ker (f.baseChange A) := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_rangeRestrict] at hx
    exact hx
  obtain ⟨z, hz⟩ := h hy
  rw [Submodule.mem_bot, ← hz]
  change f.rangeRestrict.lTensor A ((LinearMap.ker f).subtype.lTensor A z) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, rangeRestrict_comp_ker_subtype,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/--
@isnad1 id=free.1h4v.s11.75383746645a from=translated src=- shape=1d7a1dba vocab=0700dcc9
-/
theorem free_quotient_range [IsLocalRing R] [Module.Finite R M] [Module.Finite R N]
    [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) :=
  Module.free_of_lTensor_residueField_injective (LinearMap.range f).subtype
    (LinearMap.range f).mkQ (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    (lTensor_subtype_range_injective (IsLocalRing.ResidueField R) f h)

end P2mKcTorCrit

/--
@isnad1 id=free.1h4v.s11.7510fb1dfe0d from=translated src=- shape=71b764dd vocab=0700dcc9
-/
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) :=
  P2mKcTorCrit.free_quotient_range f h
