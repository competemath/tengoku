/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tautological data on stable curves

This module adds only the marked cotangent-line classes and integration needed
to define ancestor correlators. Further Gysin operations are introduced with
the first relation that consumes them.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

universe u

/-- Marked stable-curve cotangent-line classes and their primitive pullback
rules. Each class has codimension one.-/
structure PsiClasses {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) where
  /-- The cotangent-line class at a marking.-/
  psi : ∀ (g : ℕ) (S : Type) [Fintype S] (_h : StableArity g S),
    S → C.H g S
  /-- Every cotangent-line class has codimension one.-/
  psi_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (s : S),
    psi g S h s ∈ (C.H g S).degree 1
  /-- Cotangent-line classes are natural under relabelling.-/
  rename_psi : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T) (s : S),
    C.rename g S T hS hT e (psi g S hS s) = psi g T hT (e s)
  /-- Pullback to a nonseparating boundary preserves classes at the original
  markings.-/
  nonseparating_psi : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S) (s : S),
    C.nonseparating g S h (psi (g + 1) S h s) =
      psi g (Option (Option S)) (StableArity.double_option_iff.mpr h)
        (some (some s))
  /-- Pullback to a separating boundary sends a left marking to the
  corresponding class on the left tensor factor.-/
  separating_psi_left : ∀ (g₁ g₂ : ℕ) (S T : Type)
      [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (s : S),
    C.separating g₁ g₂ S T h₁ h₂
        (psi (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) (.inl s)) =
      psi g₁ (Option S) h₁ (some s) ⊗ₜ[R] 1
  /-- Pullback to a separating boundary sends a right marking to the
  corresponding class on the right tensor factor.-/
  separating_psi_right : ∀ (g₁ g₂ : ℕ) (S T : Type)
      [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (t : T),
    C.separating g₁ g₂ S T h₁ h₂
        (psi (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) (.inr t)) =
      1 ⊗ₜ[R] psi g₂ (Option T) h₂ (some t)

/-- Top-degree integration on stable-curve cohomology.-/
structure StableCurveIntegration {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) where
  /-- Integration over a stable-curve moduli space.-/
  integrate : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : StableArity g S), C.H g S →ₗ[R] R
  /-- Integration vanishes away from the complex top degree.-/
  integrate_of_degree_ne : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (d : ℕ) (x : C.H g S),
    x ∈ (C.H g S).degree d → d ≠ StableArity.dimension g S →
      integrate g S h x = 0
  /-- Integration is invariant under relabelling.-/
  integrate_rename : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
      (x : C.H g S),
    integrate g T hT (C.rename g S T hS hT e x) = integrate g S hS x

/-- Proper pushforward along the universal forgetful map. Its laws are kept
separate from pullback because a bare stable-curve cohomology system does not
carry covariant operations.-/
structure ForgetfulPushforward {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) (I : StableCurveIntegration C) where
  /-- Pushforward after forgetting the newly adjoined marking.-/
  push : ∀ (g : ℕ) (S : Type) [Fintype S] (_h : StableArity g S),
    C.H g (Option S) →ₗ[R] C.H g S
  /-- Forgetful pushforward is natural under relabelling.-/
  push_rename : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T),
    (push g T hT).comp
        (C.rename g (Option S) (Option T) (StableArity.option hS)
          (StableArity.option hT) e.optionCongr).toLinearMap =
      (C.rename g S T hS hT e).toLinearMap.comp (push g S hS)
  /-- Forgetful pushforward lowers codimension by one.-/
  push_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (d : ℕ) (x : C.H g (Option S)),
    x ∈ (C.H g (Option S)).degree (d + 1) →
      push g S h x ∈ (C.H g S).degree d
  /-- Forgetful pushforward of a degree-zero class vanishes.-/
  push_eq_zero_of_degree_zero : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (x : C.H g (Option S)),
    x ∈ (C.H g (Option S)).degree 0 → push g S h x = 0
  /-- Projection formula for forgetting a marking.-/
  projection_formula : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (x : C.H g S) (y : C.H g (Option S)),
    push g S h (C.forget g S h x * y) = x * push g S h y
  /-- Proper pushforward preserves the integral.-/
  integrate_push : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (x : C.H g (Option S)),
    I.integrate g S h (push g S h x) =
      I.integrate g (Option S) (StableArity.option h) x

namespace PsiClasses

/-- Product of powers of the marked cotangent-line classes.-/
def monomial {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (k : S → ℕ) : C.H g S :=
  ∏ s, P.psi g S h s ^ k s

@[simp]
theorem monomial_zero {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
    P.monomial g S h (fun _ ↦ 0) = 1 := by
  simp only [monomial, pow_zero, Finset.prod_const_one]

/-- A psi monomial has codimension equal to the sum of its exponents.-/
theorem monomial_degree {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (k : S → ℕ) :
    P.monomial g S h k ∈ (C.H g S).degree (∑ s, k s) := by
  classical
  unfold monomial
  induction (Finset.univ : Finset S) using Finset.induction with
  | empty =>
      exact SetLike.GradedOne.one_mem
  | @insert s markings hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs]
      apply SetLike.mul_mem_graded
      · simpa only [smul_eq_mul, mul_one]
          using SetLike.pow_mem_graded (k s) (P.psi_degree g S h s)
      · exact ih

/-- Relabelling transports a `psi` monomial by reindexing its powers.-/
theorem rename_monomial {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (k : S → ℕ) :
    C.rename g S T hS hT e (P.monomial g S hS k) =
      P.monomial g T hT (fun t ↦ k (e.symm t)) := by
  rw [monomial, map_prod]
  simp_rw [map_pow, P.rename_psi]
  simpa only [monomial, Equiv.symm_apply_apply] using
    e.prod_comp (fun t ↦ P.psi g T hT t ^ k (e.symm t))

/-- Kappa classes defined by forgetting an additional marking.-/
def kappa {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    {I : StableCurveIntegration C} (F : ForgetfulPushforward C I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (m : ℕ) : C.H g S :=
  F.push g S h (P.psi g (Option S) (StableArity.option h) none ^ (m + 1))

/-- Kappa classes are natural under relabelling of the original markings.-/
theorem kappa_rename {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    {I : StableCurveIntegration C} (F : ForgetfulPushforward C I)
    (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (m : ℕ) :
    C.rename g S T hS hT e (P.kappa F g S hS m) =
      P.kappa F g T hT m := by
  let x := P.psi g (Option S) (StableArity.option hS) none ^ (m + 1)
  have hpsi :
      C.rename g (Option S) (Option T) (StableArity.option hS)
          (StableArity.option hT) e.optionCongr x =
        P.psi g (Option T) (StableArity.option hT) none ^ (m + 1) := by
    simp only [x, map_pow, P.rename_psi]
    rfl
  have hpush := congrArg (fun f ↦ f x) (F.push_rename g S T hS hT e)
  change F.push g T hT
      (C.rename g (Option S) (Option T) (StableArity.option hS)
        (StableArity.option hT) e.optionCongr x) =
    C.rename g S T hS hT e (F.push g S hS x) at hpush
  rw [hpsi] at hpush
  exact hpush.symm

/-- The kappa class `kappa_m` has codimension `m`.-/
theorem kappa_degree {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C)
    {I : StableCurveIntegration C} (F : ForgetfulPushforward C I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (m : ℕ) :
    P.kappa F g S h m ∈ (C.H g S).degree m := by
  apply F.push_degree g S h m
  simpa only [smul_eq_mul, mul_one] using
    SetLike.pow_mem_graded (m + 1)
      (P.psi_degree g (Option S) (StableArity.option h) none)

end PsiClasses

/-- The rational-tail correction comparing a marked `psi` class with its
pullback along a forgetful map.-/
structure PsiForgetFormula {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (P : PsiClasses C) where
  /-- Boundary divisor where `s` and the forgotten marking lie on a rational
  tail.-/
  boundaryTail : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : StableArity g S), S → C.H g (Option S)
  /-- A rational-tail boundary is a divisor.-/
  boundaryTail_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (s : S),
    boundaryTail g S h s ∈ (C.H g (Option S)).degree 1
  /-- Pulling back `psi` differs from the upstairs class by the rational-tail
  boundary divisor.-/
  psi_eq_forget_add_boundary : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (s : S),
    P.psi g (Option S) (StableArity.option h) (some s) =
      C.forget g S h (P.psi g S h s) + boundaryTail g S h s

end AxiomaticGW
