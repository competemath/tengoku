/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.MvPolynomial.Rename

/-!
# `comap` operation on `MvPolynomial`

This file defines the `comap` function on `MvPolynomial`.

`MvPolynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

/-- Given an algebra hom `f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
noncomputable def comap (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) : (τ → R) → σ → R :=
  fun x i => aeval x (f (X i))

/--
@isnad1 id=eq.0h6v.s8.c8809c76ba16 from=seed src=0 shape=9602fdd2 vocab=543a2e8b
-/
@[simp]
theorem comap_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R) (i : σ) :
    comap f x i = aeval x (f (X i)) :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.552513e86223 from=seed src=0 shape=e7b6a356 vocab=25de5247
-/
@[simp]
theorem comap_id_apply (x : σ → R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x := by
  funext i
  simp only [comap, AlgHom.id_apply, aeval_X]

variable (σ R)

/--
@isnad1 id=eq.0h2v.s6.e2ad41f61fc7 from=seed src=0 shape=ee8c8f00 vocab=95952ee1
-/
theorem comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id := by
  funext x
  exact comap_id_apply x

variable {σ R}

/--
@isnad1 id=eq.0h7v.s8.bf595c747228 from=seed src=0 shape=92681ad7 vocab=6d8920ae
-/
theorem comap_comp_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) (x : υ → R) :
    comap (g.comp f) x = comap f (comap g x) := by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂Hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [comap, aeval_eq_eval₂Hom, map_eval₂Hom]
    refine eval₂Hom_congr ?_ rfl rfl
    ext r
    apply aeval_C

/--
@isnad1 id=eq.0h6v.s8.aa0b3d35ef40 from=seed src=0 shape=af50c6d6 vocab=495fb6d9
-/
theorem comap_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) : comap (g.comp f) = comap f ∘ comap g := by
  funext x
  exact comap_comp_apply _ _ _

/--
@isnad1 id=eq.1h4v.s8.9fae93dea169 from=seed src=0 shape=a744301e vocab=7b1ff710
-/
theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (hf : ∀ φ, f φ = φ)
    (x : σ → R) : comap f x = x := by
  convert! comap_id_apply x
  ext1 φ
  simp [hf, AlgHom.id_apply]

/--
@isnad1 id=eq.0h5v.s5.03cff1c7d579 from=seed src=0 shape=8a273f05 vocab=057d8e30
-/
theorem comap_rename (f : σ → τ) (x : τ → R) : comap (rename f) x = x ∘ f := by
  funext
  simp [rename_X, comap_apply, aeval_X]

/-- If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to `R`.
-/
noncomputable def comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ → R) ≃ (σ → R) where
  toFun := comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
  right_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.symm_comp]

/--
@isnad1 id=eq.0h4v.s7.17b944043596 from=seed src=0 shape=4a6da113 vocab=6a90a306
-/
@[simp]
theorem comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    (comapEquiv f : (τ → R) → σ → R) = comap f :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.d149e6f99e5b from=seed src=0 shape=2be805c6 vocab=65447db1
-/
@[simp]
theorem comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((comapEquiv f).symm : (σ → R) → τ → R) = comap f.symm :=
  rfl

end MvPolynomial
