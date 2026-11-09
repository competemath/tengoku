/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.AdditiveEquiv
import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Residue units

Constructs the quotient of valuation-ring units by first principal units and
identifies it, multiplicatively and additively, with the residue-field units.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field unit group attached to a valued field.-/
def ResidueUnits (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝓀[K]ˣ

/-- The unit group of the residue field is a commutative group.-/
instance residueUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (ResidueUnits K) := by
  change CommGroup 𝓀[K]ˣ
  infer_instance

/-- Explicit comparison with the concrete unit group of the residue field.-/
def residueUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    ResidueUnits K ≃* 𝓀[K]ˣ := by
  change 𝓀[K]ˣ ≃* 𝓀[K]ˣ
  exact MulEquiv.refl _

/-- The concrete residue-unit comparison preserves the underlying residue
unit.
@isnad1 id=eq.0h2v.s12.a66d57903c0f from=translated src=- shape=3906a6c0 vocab=eb219053
-/
@[simp]
theorem residueUnitsConcreteEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K] (u : ResidueUnits K) :
    residueUnitsConcreteEquiv K u = u :=
  rfl

/-- The unit group of the finite residue field is finite.
@isnad1 id=finite.0h1v.s7.38cabcfd81df from=translated src=- shape=7dbb90a6 vocab=3bac4619
-/
noncomputable instance residueUnitsFinite
    (K : Type u) [Field K] [ValuativeRel K] [Finite 𝓀[K]] :
    Finite (ResidueUnits K) := by
  exact Finite.of_equiv 𝓀[K]ˣ (residueUnitsConcreteEquiv K).symm.toEquiv

/-- Integer units modulo first principal units.-/
@[implicit_reducible]
def IntegerUnitsModPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K 1

/-- Valuation-ring units modulo first principal units form a commutative quotient group.-/
@[implicit_reducible]
instance integerUnitsModPrincipalUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (IntegerUnitsModPrincipalUnits K) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K 1)
  infer_instance

/-- Explicit access to the concrete quotient model.-/
def integerUnitsModPrincipalUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃*
      (𝒪[K]ˣ ⧸ principalUnits K 1) := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo first principal units.-/
@[implicit_reducible]
def integerUnitsModPrincipalUnitsMk
    (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnits K := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact QuotientGroup.mk' (principalUnits K 1)

/-- The concrete quotient equivalence sends a valuation-ring unit to its class modulo first
principal units.
@isnad1 id=eq.0h2v.s15.c122acf3af3f from=translated src=- shape=660a8e98 vocab=a3e8d034
-/
@[simp]
theorem integerUnitsModPrincipalUnitsConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsConcreteEquiv K
        (integerUnitsModPrincipalUnitsMk K x) =
      QuotientGroup.mk x :=
  rfl

/-- Eliminate a quotient class through the canonical class map.
@isnad1 id=var.0h4v.s11.676bfa68e8cd from=translated src=- shape=956a8fc9 vocab=896fd8e9
-/
protected theorem IntegerUnitsModPrincipalUnits.inductionOn
    {K : Type u} [Field K] [ValuativeRel K]
    {motive : IntegerUnitsModPrincipalUnits K → Prop}
    (q : IntegerUnitsModPrincipalUnits K)
    (h : ∀ x : 𝒪[K]ˣ, motive (integerUnitsModPrincipalUnitsMk K x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K 1 from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Descend a homomorphism that kills the first principal-unit group.-/
def integerUnitsModPrincipalUnitsLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (f : 𝒪[K]ˣ →* M) (h : principalUnits K 1 ≤ f.ker) :
    IntegerUnitsModPrincipalUnits K →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) →* M
  exact QuotientGroup.lift (principalUnits K 1) f h

/-- A map lifted from units modulo first principal units agrees with the original map on
representatives.
@isnad1 id=eq.1h4v.s13.47146dd031d2 from=translated src=- shape=a97a520a vocab=c34e83c2
-/
@[simp]
theorem integerUnitsModPrincipalUnitsLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (f : 𝒪[K]ˣ →* M) (h : principalUnits K 1 ≤ f.ker) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsLift f h
        (integerUnitsModPrincipalUnitsMk K x) = f x :=
  rfl

/-- Reduction of valuation-integer units to residue-field units.-/
def integerUnitsToResidueUnits (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* ResidueUnits K :=
  Units.map (IsLocalRing.residue 𝒪[K]).toMonoidHom

/-- Reduction of a valuation-ring unit has underlying residue equal to reduction of its underlying
integer.
@isnad1 id=eq.0h2v.s13.08fac838fcc5 from=translated src=- shape=ee114ede vocab=af4367de
-/
theorem integerUnitsToResidueUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K x) : 𝓀[K]ˣ) :
        𝓀[K]) =
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) :=
  rfl

/-- Kernel criterion for reduction on valuation-integer units.
@isnad1 id=iff.0h2v.s12.611dc6f30e40 from=translated src=- shape=8d044a93 vocab=50ddb5bc
-/
theorem mem_ker_integerUnitsToResidueUnits_iff (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    x ∈ (integerUnitsToResidueUnits K).ker ↔
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg (residueUnitsConcreteEquiv K) h
    have h'' := congrArg Units.val h'
    simpa only [integerUnitsToResidueUnits_apply, map_one, Units.val_one] using h''
  · intro h
    apply (residueUnitsConcreteEquiv K).injective
    apply Units.ext
    simpa only [integerUnitsToResidueUnits_apply, map_one, Units.val_one] using h

/-- The first principal-unit group is the kernel of reduction to residue-field units.
@isnad1 id=eq.0h1v.s10.381a70a944f0 from=translated src=- shape=50235e1b vocab=3cb1ae2c
-/
theorem principalUnits_one_eq_ker_integerUnitsToResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 1 = (integerUnitsToResidueUnits K).ker := by
  ext x
  rw [mem_principalUnits_iff, mem_ker_integerUnitsToResidueUnits_iff]
  rw [pow_one]
  rw [← sub_eq_zero]
  rw [← map_one (IsLocalRing.residue 𝒪[K]), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.symm

/-- A valuation-ring unit reduces to one exactly when it is a first principal unit.
@isnad1 id=iff.0h2v.s12.bfb8788c6a78 from=translated src=- shape=d6488080 vocab=b2122e9c
-/
theorem integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsToResidueUnits K x = 1 ↔ x ∈ principalUnits K 1 := by
  rw [principalUnits_one_eq_ker_integerUnitsToResidueUnits K, MonoidHom.mem_ker]

/-- Every residue-field unit lifts to a valuation-ring unit.
@isnad1 id=surjecti.0h1v.s11.19f2acde9066 from=translated src=- shape=5618235d vocab=da35a559
-/
theorem integerUnitsToResidueUnits_surjective (K : Type u) [Field K] [ValuativeRel K] :
    Function.Surjective (integerUnitsToResidueUnits K) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue 𝒪[K])))

/-- Reduction induces `𝒪[K]ˣ / U¹ ≃ 𝓀[K]ˣ`.-/
def integerUnitsModPrincipalUnitsEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃* ResidueUnits K :=
  (integerUnitsModPrincipalUnitsConcreteEquiv K).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (principalUnits_one_eq_ker_integerUnitsToResidueUnits K)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (integerUnitsToResidueUnits K)
        (integerUnitsToResidueUnits_surjective K)))

/-- The quotient-to-residue-unit equivalence sends a unit class to the reduction of its
representative.
@isnad1 id=eq.0h2v.s12.05afa5b3ff64 from=translated src=- shape=19bb3a84 vocab=73d3b70e
-/
@[simp]
theorem integerUnitsModPrincipalUnitsEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsMk K x) =
      integerUnitsToResidueUnits K x := by
  simp only [integerUnitsModPrincipalUnitsEquivResidueUnits, MulEquiv.trans_apply,
    integerUnitsModPrincipalUnitsConcreteEquiv_mk,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk]

/-- Additive form of `𝒪[K]ˣ / U¹ ≃ 𝓀[K]ˣ`.-/
def integerUnitsModPrincipalUnitsAddEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    Additive (IntegerUnitsModPrincipalUnits K) ≃+ Additive (ResidueUnits K) :=
  additiveEquivOfMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits K)

/-- Equality in `𝒪[K]ˣ / U¹`, expressed by a first-principal-unit quotient.
@isnad1 id=iff.0h3v.s13.ad0f741f2335 from=translated src=- shape=be899f3c vocab=b7d11746
-/
theorem IntegerUnitsModPrincipalUnits_mk_eq_mk_iff
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x =
        integerUnitsModPrincipalUnitsMk K y ↔
      x / y ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) =
      QuotientGroup.mk y ↔ _
    exact QuotientGroup.eq_iff_div_mem (N := principalUnits K 1)

/-- Triviality criterion in `𝒪[K]ˣ / U¹`.
@isnad1 id=iff.0h2v.s12.9bb15ce85190 from=translated src=- shape=d6488080 vocab=6813df1b
-/
theorem IntegerUnitsModPrincipalUnits_mk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x = 1 ↔
      x ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) = 1 ↔ _
    exact QuotientGroup.eq_one_iff (N := principalUnits K 1) x

/-- Additive version of the residue-unit quotient equivalence on quotient representatives.
@isnad1 id=eq.0h2v.s12.7aad18be497f from=translated src=- shape=f02b6fce vocab=9a531636
-/
@[simp]
theorem integerUnitsModPrincipalUnitsAddEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAddEquivResidueUnits K
        (Additive.ofMul (integerUnitsModPrincipalUnitsMk K x)) =
      Additive.ofMul (integerUnitsToResidueUnits K x) := by
  exact congrArg Additive.ofMul
    (integerUnitsModPrincipalUnitsEquivResidueUnits_mk K x)

/-- Module form of the residue-unit quotient equivalence.-/
def integerUnitsModPrincipalUnitsIsoResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    CategoryTheory.Iso (ModuleCat.of ℤ (Additive (IntegerUnitsModPrincipalUnits K)))
      (ModuleCat.of ℤ (Additive (ResidueUnits K))) :=
  (integerUnitsModPrincipalUnitsAddEquivResidueUnits K).toIntLinearEquiv.toModuleIso

end
end LocalFieldTheory
