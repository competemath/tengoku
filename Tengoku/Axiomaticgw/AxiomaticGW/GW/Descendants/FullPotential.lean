/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Descendants.Equations
public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Descendants.Potentials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unstable descendant conventions

Stable-map descendants in this project land in stable-curve cohomology and
therefore exist only for stable curve arities. This file permits the missing
numerical unstable correlators to be supplied explicitly. It does not assign
positive-degree unstable invariants by fiat.

The stable string and dilaton laws and the exceptional unstable recurrences
together imply equations valid for every finite marking type.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

/-- Combine stable descendant invariants with an explicitly supplied family
of unstable numerical correlators.-/
noncomputable def extendedDescendantInvariant
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    (unstable : ∀ (_g : ℕ) (S : Type) [Fintype S], B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) R)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ)
    (a : S → V) : R := by
  classical
  exact if h : StableArity g S then M.invariant I g S h beta k a
    else unstable g S beta k a

/-- Explicit conventions for arities not represented by stable-curve
cohomology. The recurrence fields include transitions from an unstable arity
to a stable one, which is where the metric correction enters the global
string equation.-/
structure UnstableDescendantConventions
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C) where
  /-- Numerical correlators outside stable curve arities. Values in positive
  curve class are data, not consequences of the current axioms.-/
  unstableInvariant : ∀ (_g : ℕ) (S : Type) [Fintype S],
    B → (S → ℕ) → MultilinearMap R (fun _ : S ↦ V) R
  /-- Genus-zero zero-point normalization in degree zero.-/
  zeroPoint_zero :
    unstableInvariant 0 Empty 0 (fun s ↦ nomatch s) (fun s ↦ nomatch s) = 0
  /-- Genus-zero one-point normalization in degree zero.-/
  onePoint_zero : ∀ (k : Fin 1 → ℕ) (a : Fin 1 → V),
    unstableInvariant 0 (Fin 1) 0 k a = 0
  /-- The exceptional genus-zero two-point primary correlator is the metric.-/
  twoPoint_zero : ∀ (a : Fin 2 → V),
    unstableInvariant 0 (Fin 2) 0 (fun _ ↦ 0) a =
      Omega.pairing.form (a 0) (a 1)
  /-- String recurrence whenever the base arity is unstable. The left side
  may already be stable, notably for the `0,2` to `0,3` transition.-/
  string_unstable : ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (_h : ¬StableArity g S) (beta : B) (k : S → ℕ) (a : S → V),
    extendedDescendantInvariant M I unstableInvariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ∑ s, if k s = 0 then 0 else
        extendedDescendantInvariant M I unstableInvariant g S beta
          (lowerPower k s) a
  /-- Dilaton recurrence whenever the base arity is unstable.-/
  dilaton_unstable : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : ¬StableArity g S) (beta : B) (k : S → ℕ) (a : S → V),
    extendedDescendantInvariant M I unstableInvariant g (Option S) beta
        (fun | none => 1 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ((2 * g + Fintype.card S - 2 : ℕ) : R) *
        extendedDescendantInvariant M I unstableInvariant g S beta k a

namespace UnstableDescendantConventions

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Numerical descendant invariant for every arity.-/
noncomputable def invariant (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ)
    (a : S → V) : R :=
  extendedDescendantInvariant M I U.unstableInvariant g S beta k a

/-- On stable arities the extension is definitionally governed by the
existing stabilized descendant invariant.-/
theorem invariant_of_stable (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g S beta k a = M.invariant I g S h beta k a := by
  simp only [invariant, extendedDescendantInvariant, h, ↓reduceDIte,
    StableMapDescendants.invariant_apply]

/-- On unstable arities the extension uses exactly the supplied convention.-/
theorem invariant_of_unstable (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (h : ¬StableArity g S)
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g S beta k a = U.unstableInvariant g S beta k a := by
  simp only [invariant, extendedDescendantInvariant, h, ↓reduceDIte]

/-- String equation for every arity, derived by separating the stable law
from the explicitly supplied exceptional recurrences.-/
theorem global_string (U : UnstableDescendantConventions M I)
    (L : DescendantStringDilatonLaws M I)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ∑ s, if k s = 0 then 0 else
        U.invariant g S beta (lowerPower k s) a := by
  by_cases h : StableArity g S
  · rw [U.invariant_of_stable g (Option S) (StableArity.option h)]
    calc
      M.invariant I g (Option S) (StableArity.option h) beta
          (fun | none => 0 | some s => k s)
          (fun | none => Omega.unit | some s => a s) =
          ∑ s, if k s = 0 then 0 else
            M.invariant I g S h beta (lowerPower k s) a :=
        L.string g S h beta k a
      _ = ∑ s, if k s = 0 then 0 else
          U.invariant g S beta (lowerPower k s) a := by
        apply Finset.sum_congr rfl
        intro s _hs
        split_ifs
        · rfl
        · rw [U.invariant_of_stable g S h]
  · exact U.string_unstable g S h beta k a

/-- Dilaton equation for every arity.-/
theorem global_dilaton (U : UnstableDescendantConventions M I)
    (L : DescendantStringDilatonLaws M I)
    (g : ℕ) (S : Type) [Fintype S]
    (beta : B) (k : S → ℕ) (a : S → V) :
    U.invariant g (Option S) beta
        (fun | none => 1 | some s => k s)
        (fun | none => Omega.unit | some s => a s) =
      ((2 * g + Fintype.card S - 2 : ℕ) : R) *
        U.invariant g S beta k a := by
  by_cases h : StableArity g S
  · rw [U.invariant_of_stable g (Option S) (StableArity.option h)]
    calc
      M.invariant I g (Option S) (StableArity.option h) beta
          (fun | none => 1 | some s => k s)
          (fun | none => Omega.unit | some s => a s) =
          ((2 * g + Fintype.card S - 2 : ℕ) : R) *
            M.invariant I g S h beta k a :=
        L.dilaton g S h beta k a
      _ = ((2 * g + Fintype.card S - 2 : ℕ) : R) *
          U.invariant g S beta k a := by
        rw [U.invariant_of_stable g S h]
  · exact U.dilaton_unstable g S h beta k a

/-- Full genus-`g` descendant potential, including explicitly supplied
unstable coefficients.-/
noncomputable def fullDescendantPotential
    (U : UnstableDescendantConventions M I) (b : Basis ι R V) (g : ℕ) :
    FormalPotential D (DescendantVariable ι) R := by
  classical
  intro n beta
  exact profileWeight R n *
    U.invariant g (InsertionLabel n) beta
      (InsertionLabel.power (n := n)) (InsertionLabel.state (n := n) b)

/-- The full potential agrees with the existing stable potential at every
stable profile.-/
theorem fullDescendantPotential_coeff_of_stable
    (U : UnstableDescendantConventions M I) (b : Basis ι R V) (g : ℕ)
    (n : DescendantVariable ι →₀ ℕ) (beta : B)
    (h : StableArity g (InsertionLabel n)) :
    U.fullDescendantPotential b g n beta =
      Omega.descendantPotential M I b g n beta := by
  rw [GromovWittenTheory.descendantPotential_coeff_of_stable _ _ _ _ _ _ _ h]
  simp only [fullDescendantPotential]
  rw [U.invariant_of_stable g (InsertionLabel n) h]

/-- At an unstable profile, the coefficient is exactly the declared
convention with the standard multiplicity weight.-/
theorem fullDescendantPotential_coeff_of_unstable
    (U : UnstableDescendantConventions M I) (b : Basis ι R V) (g : ℕ)
    (n : DescendantVariable ι →₀ ℕ) (beta : B)
    (h : ¬StableArity g (InsertionLabel n)) :
    U.fullDescendantPotential b g n beta =
      profileWeight R n * U.unstableInvariant g (InsertionLabel n) beta
        (InsertionLabel.power (n := n)) (InsertionLabel.state (n := n) b) := by
  simp only [fullDescendantPotential]
  rw [U.invariant_of_unstable g (InsertionLabel n) h]

end UnstableDescendantConventions

end AxiomaticGW
