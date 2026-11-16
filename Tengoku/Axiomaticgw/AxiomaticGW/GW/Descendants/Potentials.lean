/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Coefficients.GenusExpansion
public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Descendants.Comparison
public import Tengoku.Seed.Data.Nat.Factorial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Potentials constructed from GW invariants

A finitely supported monomial determines a canonical finite label type: one
label for every occurrence of every descendant variable. This removes all
ordering choices and makes the usual multiplicity-factorial normalization
literal in the coefficient definition. The constructed genus potentials
retain only stable curve arities; unstable coefficients are set to zero by
definition and are not claims about positive-degree stable-map invariants.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

/-- Product of the factorials of all variable multiplicities.-/
def profileFactorial {Vars : Type*} (n : Vars →₀ ℕ) : ℕ :=
  n.prod fun _ multiplicity ↦ Nat.factorial multiplicity

/-- The reciprocal multiplicity factorial in a rational coefficient ring.-/
def profileWeight (R : Type*) [CommRing R] [Algebra ℚ R]
    {Vars : Type*} (n : Vars →₀ ℕ) : R :=
  algebraMap ℚ R ((profileFactorial n : ℚ)⁻¹)

/-- One label for each occurrence recorded by a finite multiplicity profile.-/
abbrev InsertionLabel {Vars : Type*} (n : Vars →₀ ℕ) :=
  Σ v : n.support, Fin (n v.1)

namespace InsertionLabel

variable {Vars : Type*} {ι : Type*} {n : DescendantVariable ι →₀ ℕ}

/-- Formal variable attached to an occurrence label.-/
def formalVariable {m : Vars →₀ ℕ} (s : InsertionLabel m) : Vars :=
  s.1.1

/-- Descendant variable attached to an occurrence label.-/
def descendantVar (s : InsertionLabel n) : DescendantVariable ι :=
  s.1.1

/-- Cotangent power attached to an occurrence label.-/
def power (s : InsertionLabel n) : ℕ :=
  (descendantVar s).1

/-- State-space basis index attached to an occurrence label.-/
def basisIndex (s : InsertionLabel n) : ι :=
  (descendantVar s).2

/-- Basis state inserted at an occurrence label.-/
noncomputable def state {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V]
    (b : Basis ι R V) (s : InsertionLabel n) : V :=
  b (basisIndex s)

/-- Basis state attached to an occurrence of a primary variable.-/
noncomputable def primaryState {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] {m : ι →₀ ℕ}
    (b : Basis ι R V) (s : InsertionLabel m) : V :=
  b (formalVariable s)

end InsertionLabel

/-- Retain exactly the monomials belonging to stable genus-`g` arities.-/
noncomputable def stablePart {B Vars R : Type*} [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) [CommRing R] (g : ℕ) :
    FormalPotential D Vars R →ₗ[NovikovSeries D R]
      FormalPotential D Vars R := by
  classical
  exact
    { toFun := fun f n ↦
        if StableArity g (InsertionLabel n) then f n else 0
      map_add' := by
        intro f h
        funext n
        change (if StableArity g (InsertionLabel n) then (f + h) n else 0) =
          (if StableArity g (InsertionLabel n) then f n else 0) +
            if StableArity g (InsertionLabel n) then h n else 0
        by_cases hn : StableArity g (InsertionLabel n)
        · simp only [hn, ite_eq_left]
          rfl
        · simp only [hn, ↓reduceIte, add_zero]
      map_smul' := by
        intro q f
        funext n
        change (if StableArity g (InsertionLabel n) then (q • f) n else 0) =
          q • if StableArity g (InsertionLabel n) then f n else 0
        by_cases hn : StableArity g (InsertionLabel n)
        · simp only [hn, ite_eq_left]
          rfl
        · simp only [hn, ↓reduceIte, smul_eq_mul, mul_zero] }

/-- Differentiate a descendant potential by inserting `x` with cotangent
power `k`. The finite support of `b.repr x` makes the directional derivative
a finite sum even when the basis index type is infinite.-/
noncomputable def insertionDerivative
    {R V B : Type*} {ι : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (b : Basis ι R V) (k : ℕ) (x : V) :
    FormalPotential D (DescendantVariable ι) R →
      FormalPotential D (DescendantVariable ι) R := fun f ↦
  (b.repr x).sum fun i r ↦ r •
    MvPowerSeries.pderiv (R := NovikovSeries D R) (k, i) f

/--
@isnad1 id=eq.0h9v.s9.3231ae665149 from=translated src=- shape=23db3f1a vocab=6c096d55
-/
@[simp]
theorem insertionDerivative_basis
    {R V B : Type*} {ι : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (b : Basis ι R V) (k : ℕ) (i : ι)
    (f : FormalPotential D (DescendantVariable ι) R) :
    insertionDerivative D b k (b i) f =
      MvPowerSeries.pderiv (R := NovikovSeries D R) (k, i) f := by
  classical
  simp only [insertionDerivative, Basis.repr_self]
  rw [Finsupp.sum_single_index (by
    rw [Algebra.smul_def, map_zero, zero_mul])]
  rw [Algebra.smul_def, map_one, one_mul]

namespace GromovWittenTheory

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- Genus-`g` descendant potential constructed from stabilized descendant
invariants in a chosen state-space basis.-/
noncomputable def descendantPotential (Omega : GromovWittenTheory R V B D C)
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) :
    FormalPotential D (DescendantVariable ι) R := by
  classical
  intro n beta
  exact if h : StableArity g (InsertionLabel n) then
    profileWeight R n *
      M.invariant I g (InsertionLabel n) h beta
        (InsertionLabel.power (n := n)) (InsertionLabel.state (n := n) b)
    else 0

/-- Genus-`g` ancestor potential constructed from stable-curve psi classes.-/
noncomputable def ancestorPotential (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) :
    FormalPotential D (DescendantVariable ι) R := by
  classical
  intro n beta
  exact if h : StableArity g (InsertionLabel n) then
    profileWeight R n *
      Omega.ancestorInvariant P I g (InsertionLabel n) h beta
        (InsertionLabel.power (n := n)) (InsertionLabel.state (n := n) b)
    else 0

/-- Descendant and ancestor potentials produced by one GW theory.-/
noncomputable def potentials (Omega : GromovWittenTheory R V B D C)
    (M : StableMapDescendants Omega) (P : PsiClasses C)
    (I : StableCurveIntegration C) (b : Basis ι R V) :
    GWPotentials D (DescendantVariable ι) R where
  descendant := Omega.descendantPotential M I b
  ancestor := Omega.ancestorPotential P I b

/--
@isnad1 id=eq.1h13v.s9.9973e331c45f from=translated src=- shape=91c7816f vocab=b5b2643a
-/
theorem descendantPotential_coeff_of_stable
    (Omega : GromovWittenTheory R V B D C)
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) (n : DescendantVariable ι →₀ ℕ)
    (beta : B) (h : StableArity g (InsertionLabel n)) :
    Omega.descendantPotential M I b g n beta =
      profileWeight R n *
        M.invariant I g (InsertionLabel n) h beta
          (InsertionLabel.power (n := n))
          (InsertionLabel.state (n := n) b) := by
  classical
  simp only [descendantPotential, h, ↓reduceDIte,
    StableMapDescendants.invariant_apply]

/--
@isnad1 id=eq.1h13v.s8.e3c3fd1d88dd from=translated src=- shape=fabb014a vocab=6ee315f2
-/
theorem descendantPotential_coeff_of_unstable
    (Omega : GromovWittenTheory R V B D C)
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) (n : DescendantVariable ι →₀ ℕ)
    (beta : B) (h : ¬StableArity g (InsertionLabel n)) :
    Omega.descendantPotential M I b g n beta = 0 := by
  classical
  simp only [descendantPotential, h, ↓reduceDIte]

/--
@isnad1 id=eq.1h13v.s9.d1f10f1da56e from=translated src=- shape=36f9f8ec vocab=7a8995bc
-/
theorem ancestorPotential_coeff_of_stable
    (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) (n : DescendantVariable ι →₀ ℕ)
    (beta : B) (h : StableArity g (InsertionLabel n)) :
    Omega.ancestorPotential P I b g n beta =
      profileWeight R n *
        Omega.ancestorInvariant P I g (InsertionLabel n) h beta
          (InsertionLabel.power (n := n))
          (InsertionLabel.state (n := n) b) := by
  classical
  simp only [ancestorPotential, h, ↓reduceDIte, ancestorInvariant_apply]

/--
@isnad1 id=eq.1h13v.s8.41e7d0206661 from=translated src=- shape=04447f3d vocab=c9dbafd4
-/
theorem ancestorPotential_coeff_of_unstable
    (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) (n : DescendantVariable ι →₀ ℕ)
    (beta : B) (h : ¬StableArity g (InsertionLabel n)) :
    Omega.ancestorPotential P I b g n beta = 0 := by
  classical
  simp only [ancestorPotential, h, ↓reduceDIte]

end GromovWittenTheory

namespace DescendantAncestorComparison

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {P : PsiClasses C} {M : StableMapDescendants Omega}

/-- Generating series of the recorded descendant--ancestor residuals.-/
noncomputable def boundaryPotential (X : DescendantAncestorComparison P M)
    (I : StableCurveIntegration C) (b : Basis ι R V) (g : ℕ) :
    FormalPotential D (DescendantVariable ι) R := by
  classical
  intro n beta
  exact if h : StableArity g (InsertionLabel n) then
    profileWeight R n * I.integrate g (InsertionLabel n) h
      (X.boundaryCorrection g (InsertionLabel n) h beta
        (InsertionLabel.power (n := n))
        (InsertionLabel.state (n := n) b))
    else 0

/-- Descendant potentials equal ancestor potentials plus their recorded
residual series. This identity does not establish geometric boundary support.
@isnad1 id=eq.0h13v.s8.1bef7c1baa33 from=translated src=- shape=6c7eff33 vocab=9e7edabf
-/
theorem descendantPotential_eq_ancestor_add_boundary
    (X : DescendantAncestorComparison P M) (I : StableCurveIntegration C)
    (b : Basis ι R V) (g : ℕ) :
    Omega.descendantPotential M I b g =
      Omega.ancestorPotential P I b g + X.boundaryPotential I b g := by
  classical
  funext n beta
  change Omega.descendantPotential M I b g n beta =
    Omega.ancestorPotential P I b g n beta +
      X.boundaryPotential I b g n beta
  by_cases h : StableArity g (InsertionLabel n)
  · rw [GromovWittenTheory.descendantPotential_coeff_of_stable _ _ _ _ _ _ _ h,
      GromovWittenTheory.ancestorPotential_coeff_of_stable _ _ _ _ _ _ _ h]
    simp only [boundaryPotential, h, dite_true]
    have hcomparison := congrArg
      (fun f ↦ f (InsertionLabel.state (n := n) b))
      (X.invariant_eq_ancestor_add_boundary I g (InsertionLabel n) h beta
        (InsertionLabel.power (n := n)))
    simp only [add_apply, LinearMap.compMultilinearMap_apply] at hcomparison
    rw [hcomparison, mul_add]
  · rw [GromovWittenTheory.descendantPotential_coeff_of_unstable _ _ _ _ _ _ _ h,
      GromovWittenTheory.ancestorPotential_coeff_of_unstable _ _ _ _ _ _ _ h]
    simp only [boundaryPotential, h, ↓reduceDIte, add_zero]

end DescendantAncestorComparison

end AxiomaticGW
