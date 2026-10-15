/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
 # Some obvious lemmas on module.End

This file contains some obvious lemmas on `module.End`.
-/

@[expose] public section

open scoped BigOperators

/--
@isnad1 id=eq.0h4v.s7.3f00548b0911 from=translated src=- shape=265f7f3d vocab=a3000c68
-/
theorem LinearMap.comp_one {R E F : Type _} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R F] [Module R E] (f : E →ₗ[R] F) : f ∘ₗ (1 : E →ₗ[R] E) = f := rfl

/--
@isnad1 id=eq.0h4v.s7.63feebd5b28a from=translated src=- shape=fb2889d6 vocab=a3000c68
-/
theorem LinearMap.one_comp {R E F : Type _} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R F] [Module R E] (f : E →ₗ[R] F) : (1 : F →ₗ[R] F) ∘ₗ f = f := rfl

/--
@isnad1 id=eq.0h8v.s7.ddb288492547 from=translated src=- shape=31be951c vocab=1c576060
-/
theorem LinearMap.comp_sum {R M M₂ M₃ : Type _} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
    [AddCommMonoid M₃] [Module R M] [Module R M₂] [Module R M₃] (g : M₃ →ₗ[R] M₂) {α : Type _}
    (s : Finset α) (f : α → M →ₗ[R] M₃) : g ∘ₗ ∑ a ∈ s, f a = ∑ a ∈ s, g ∘ₗ f a := by
  simp_rw [LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    map_sum, forall_true_iff]

/--
@isnad1 id=eq.0h8v.s7.220df81a6253 from=translated src=- shape=acf58244 vocab=1c576060
-/
theorem LinearMap.sum_comp {R M M₂ M₃ : Type _} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
    [AddCommMonoid M₃] [Module R M] [Module R M₂] [Module R M₃] (f : M →ₗ[R] M₃) {α : Type _}
    (s : Finset α) (g : α → M₃ →ₗ[R] M₂) : (∑ a ∈ s, g a) ∘ₗ f = ∑ a ∈ s, g a ∘ₗ f := by
  simp_rw [LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    forall_true_iff]

/--
@isnad1 id=iff.0h4v.s7.6c13982fbef3 from=translated src=- shape=a4ff99a9 vocab=cc9883f8
-/
theorem Module.End.has_eigenvector_iff_hasEigenvalue {R M : Type _} [CommRing R] [AddCommGroup M]
    [Module R M] {T : Module.End R M} {α : R} :
    (∃ v : M, T v = α • v ∧ v ≠ 0) ↔ Module.End.HasEigenvalue T α := by
  constructor
  · rintro ⟨v, hv⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    rwa [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  · intro h
    simp only [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue] at h
    simp_rw [Submodule.ne_bot_iff] at h
    simp_all
