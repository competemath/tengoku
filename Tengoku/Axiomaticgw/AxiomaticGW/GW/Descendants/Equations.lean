/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Coefficients.GenusExpansion
public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Descendants.Comparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descendant equations

String, dilaton, and divisor equations require more than the minimal primary
GW axioms. This structure records those optional laws at the stable-correlator
level, before translating them into differential equations for potentials.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Lower the cotangent power at one named marking.-/
def lowerPower {S : Type*} [DecidableEq S] (k : S → ℕ) (s : S) : S → ℕ :=
  Function.update k s (k s - 1)

/-- Replace one named state-space insertion.-/
def replaceInput {S V : Type*} [DecidableEq S]
    (a : S → V) (s : S) (x : V) : S → V :=
  Function.update a s x

/-- Optional stable string and dilaton equations. These laws require descendant
invariants and integration, but no divisor-specific data.-/
structure DescendantStringDilatonLaws
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C) where
  /-- Stable string equation.-/
  string : ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V),
    M.invariant I g (Option S) (StableArity.option h) beta
        (fun | none => 0 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ∑ s, if k s = 0 then 0 else
        M.invariant I g S h beta (lowerPower k s) a
  /-- Stable dilaton equation.-/
  dilaton : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V),
    M.invariant I g (Option S) (StableArity.option h) beta
        (fun | none => 1 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ((2 * g + Fintype.card S - 2 : ℕ) : R) *
        M.invariant I g S h beta k a

/-- Optional stable descendant divisor equation. The primary divisor axiom
supplies the divisor--curve pairing, while `divisorAction` is a bilinear
choice of cup product by divisor states.-/
structure DescendantDivisorLaw
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    {F : ForgetfulPushforward C I} (A : GWDivisorAxiom Omega F) where
  /-- Cup product by a divisor state, linear in both the divisor and the state.-/
  divisorAction : Omega.graded.degree 1 →ₗ[R] Module.End R V
  /-- Descendant divisor equation, including the terms that lower a positive
  cotangent power.-/
  divisor : ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V)
      (divisorState : Omega.graded.degree 1),
    M.invariant I g (Option S) (StableArity.option h) beta
        (fun | none => 0 | some s => k s)
        (fun | none => divisorState.1 | some s => a s) =
      A.divisorPairing divisorState beta * M.invariant I g S h beta k a +
        ∑ s, if k s = 0 then 0 else
          M.invariant I g S h beta (lowerPower k s)
            (replaceInput a s (divisorAction divisorState (a s)))

/-- The full optional package of stable string, dilaton, and divisor laws.-/
structure DescendantEquationLaws
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    {F : ForgetfulPushforward C I} (A : GWDivisorAxiom Omega F) extends
      DescendantStringDilatonLaws M I, DescendantDivisorLaw M I A

end AxiomaticGW
