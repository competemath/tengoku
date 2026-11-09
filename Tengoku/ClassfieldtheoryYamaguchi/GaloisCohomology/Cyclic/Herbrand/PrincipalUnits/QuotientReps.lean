/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientReps` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Integer units modulo the `n`-th principal-unit subgroup.

This named type is the representation boundary: downstream code uses its
quotient interface rather than unfolding the concrete quotient.-/
def IntegerUnitsModPrincipalUnitsAtLevel
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n

/-- Integer units modulo level principal units form a commutative group.-/
instance integerUnitsModPrincipalUnitsAtLevelCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance

/-- Explicit comparison with the concrete quotient implementation.-/
def integerUnitsModPrincipalUnitsAtLevelConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      (𝒪[K]ˣ ⧸ principalUnits K n) := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K n)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo `U_K^n`.-/
def integerUnitsModPrincipalUnitsAtLevelMk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnitsAtLevel K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)

/-- The concrete quotient equivalence sends a unit to its canonical class.
@isnad1 id=eq.0h3v.s15.a2ddc407f49c from=translated src=- shape=a2aa43e3 vocab=c36fad0d
-/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K n
        (integerUnitsModPrincipalUnitsAtLevelMk K n x) =
      QuotientGroup.mk x :=
  rfl

/-- Every integer-unit quotient class has a representative.
@isnad1 id=surjecti.0h2v.s11.7ecc378d72bc from=translated src=- shape=5eb022e2 vocab=b3267020
-/
theorem integerUnitsModPrincipalUnitsAtLevelMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Surjective (integerUnitsModPrincipalUnitsAtLevelMk K n) := by
  change Function.Surjective (QuotientGroup.mk' (principalUnits K n))
  exact QuotientGroup.mk'_surjective (principalUnits K n)

/-- Eliminate a level quotient through its canonical representatives.
@isnad1 id=var.0h5v.s11.e9645117eb5b from=translated src=- shape=03675669 vocab=90004fe2
-/
protected theorem IntegerUnitsModPrincipalUnitsAtLevel.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsModPrincipalUnitsAtLevel K n → Prop}
    (q : IntegerUnitsModPrincipalUnitsAtLevel K n)
    (h : ∀ x : 𝒪[K]ˣ,
      motive (integerUnitsModPrincipalUnitsAtLevelMk K n x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Descend a homomorphism that kills `U_K^n`.-/
def integerUnitsModPrincipalUnitsAtLevelLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker) :
    IntegerUnitsModPrincipalUnitsAtLevel K n →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) →* M
  exact QuotientGroup.lift (principalUnits K n) f h

/-- A map lifted from the integer-unit quotient agrees on representatives.
@isnad1 id=eq.1h5v.s13.4ef3abb67320 from=translated src=- shape=13d9a368 vocab=3665013f
-/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelLift n f h
        (integerUnitsModPrincipalUnitsAtLevelMk K n x) = f x :=
  rfl

/-- A unit represents the identity exactly when it lies in the level principal-unit subgroup.
@isnad1 id=iff.0h3v.s12.c3ba884e92fe from=translated src=- shape=c4e9abcf vocab=e6a44233
-/
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔
      x ∈ principalUnits K n := by
  change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) = 1 ↔ _
  exact QuotientGroup.eq_one_iff x

/-- Two units represent the same class exactly when their quotient is a level principal unit.
@isnad1 id=iff.0h4v.s13.56caa3e204f7 from=translated src=- shape=73effcd6 vocab=37eff984
-/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk K n x =
        integerUnitsModPrincipalUnitsAtLevelMk K n y ↔
      x / y ∈ principalUnits K n := by
  change
    (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) =
      QuotientGroup.mk y ↔ _
  exact QuotientGroup.eq_iff_div_mem

end

end CyclicCohomology
