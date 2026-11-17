/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Coefficients.EffectiveCurveClass
public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Ancestors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primary Gromov--Witten theory

The class family is coefficientwise in an effective curve class. Numerical
and finite-free state-valued operations support Novikov completion, while an
arbitrary cohomology target remains coefficientwise as specified by D14.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Codimension equation for a homogeneous primary GW class. Written without
subtraction, it says `q = inputDegree + (g - 1) * dimension - c1(beta)`.-/
def GWOutputDegree (dimension g inputDegree q : ℕ) (c1Degree : ℤ) : Prop :=
  (q : ℤ) + (dimension : ℤ) + c1Degree =
    (inputDegree : ℤ) + (g : ℤ) * (dimension : ℤ)

/-- An all-genus primary Gromov--Witten theory resolved by effective numerical
curve class. This is an axiomatic class package; it does not construct
stable-map spaces or virtual fundamental classes.-/
structure GromovWittenTheory (R V B : Type u) [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] (D : EffectiveCurveMonoid B)
    (C : StableCurveCohomology R) where
  /-- Metric used at every node.-/
  pairing : SymmetricPerfectPairing R V
  /-- Flat unit insertion.-/
  unit : V
  /-- State-space grading and Poincare duality dimension.-/
  graded : GradedStateSpace R V pairing unit
  /-- First-Chern number of a curve class.-/
  c1Degree : B →+ ℤ
  /-- Primary class in a fixed effective curve class.-/
  omega : (g : ℕ) → (S : Type) → [Fintype S] →
    (h : StableArity g S) → B →
      MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Simultaneous relabelling of markings and inputs.-/
  relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T) (beta : B),
    (C.rename g S T hS hT e).toLinearMap.compMultilinearMap
        ((omega g S hS beta).domDomCongr e) = omega g T hT beta
  /-- Flat-unit insertion is coefficientwise forgetful pullback.-/
  unit_insert : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (a : S → V),
    omega g (Option S) (StableArity.option h) beta
        (fun | none => unit | some s => a s) =
      C.forget g S h (omega g S h beta a)
  /-- Nonseparating gluing preserves the curve class.-/
  nonseparating : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S) (beta : B),
    pairing.selfContractTarget
        ((omega g (Option (Option S))
          (StableArity.double_option_iff.mpr h) beta).domDomCongr
            (doubleOptionEquiv S)) =
      (C.nonseparating g S h).toLinearMap.compMultilinearMap
        (omega (g + 1) S h beta)
  /-- Separating gluing is convolution over all splittings of the curve class.-/
  separating : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (beta : B),
    (∑ split ∈ D.splittings beta,
      pairing.pairContractTarget
        (omega g₁ (Option S) h₁ split.1)
        (omega g₂ (Option T) h₂ split.2)) =
      (C.separating g₁ g₂ S T h₁ h₂).toLinearMap.compMultilinearMap
        (omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) beta)
  /-- The beta-zero three-point class with a unit insertion is the metric.-/
  normalization_zero : ∀ a : Fin 2 → V,
    omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two 0
        (fun | none => unit | some i => a i) =
      algebraMap R (C.H 0 (Option (Fin 2))) (pairing.form (a 0) (a 1))
  /-- A positive curve class has zero three-point class after inserting the
  flat unit.-/
  normalization_nonzero : ∀ (beta : B), beta ≠ 0 → ∀ a : Fin 2 → V,
    omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta
        (fun | none => unit | some i => a i) = 0
  /-- A homogeneous input family produces the codimension prescribed by the
  virtual-dimension formula.-/
  omega_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (p : S → ℕ) (a : S → V) (q : ℕ),
    (∀ s, a s ∈ graded.degree (p s)) →
      GWOutputDegree graded.dimension g (∑ s, p s) q (c1Degree beta) →
        omega g S h beta a ∈ (C.H g S).degree q
  /-- If the expected codimension is negative, the primary class vanishes.-/
  omega_eq_zero_of_negative : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (p : S → ℕ) (a : S → V),
    (∀ s, a s ∈ graded.degree (p s)) →
      ((∑ s, p s : ℕ) : ℤ) + (g : ℤ) * (graded.dimension : ℤ) <
        (graded.dimension : ℤ) + c1Degree beta →
      omega g S h beta a = 0

/-- The divisor axiom is an optional extension because it requires proper
forgetful pushforward and target-specific divisor--curve pairing data.-/
structure GWDivisorAxiom {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} (Omega : GromovWittenTheory R V B D C)
    {I : StableCurveIntegration C} (F : ForgetfulPushforward C I) where
  /-- Pairing between divisor states and effective curve classes.-/
  divisorPairing : Omega.graded.degree 1 →ₗ[R] (B →+ R)
  /-- Stable primary divisor equation.-/
  divisor : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (a : S → V)
      (divisorState : Omega.graded.degree 1),
    F.push g S h
        (Omega.omega g (Option S) (StableArity.option h) beta
          (fun | none => divisorState.1 | some s => a s)) =
      divisorPairing divisorState beta • Omega.omega g S h beta a

end AxiomaticGW
