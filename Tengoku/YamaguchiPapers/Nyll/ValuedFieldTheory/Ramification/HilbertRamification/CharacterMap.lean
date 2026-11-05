/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert ramification theory: character-map source

This file records the source lemmas for the canonical map
`I_w -> Hom(Delta / Gamma, lambda*)` in prime-decomposition theory.  We do not
package the final value-group quotient here.  Instead, we prove the pieces
which make the formula

`x ↦ (σ x / x) mod U^1`

independent of the unit and base-unit choices used to represent a value class,
and we identify the ramification group as the subgroup on which all these
classes are trivial.
-/

namespace RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The unit quotient is multiplicative in the unit argument.
@isnad1 id=eq.0h6v.s8.eabbc657b4be from=translated src=- shape=e25c22b7 vocab=a56f3682
-/
theorem automorphismUnitQuotient_mul_arg
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A)
    (x y : Lˣ) :
    automorphismUnitQuotient K A σ (x * y) =
      automorphismUnitQuotient K A σ x *
        automorphismUnitQuotient K A σ y := by
  ext
  simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm]

/-- The unit quotient is trivial on the unit `1`.
@isnad1 id=eq.0h4v.s8.683f13bd727e from=translated src=- shape=3f9c63ef vocab=9415e3f6
-/
theorem automorphismUnitQuotient_one_arg
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) :
    automorphismUnitQuotient K A σ 1 = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- A `K`-unit contributes trivially to the unit quotient.
@isnad1 id=eq.0h5v.s9.7600e67097e3 from=translated src=- shape=bbe55e84 vocab=38e5a6dd
-/
theorem automorphismUnitQuotient_algebraMapUnit
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (a : Kˣ) :
    automorphismUnitQuotient K A σ
        (Units.map (algebraMap K L).toMonoidHom a) = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- Prime-decomposition statement:
an inertia element sends valuation-ring units to the same residue class, hence
its unit quotient on such a unit is principal.
@isnad1 id=mem.1h5v.s11.0058d98e1655 from=translated src=- shape=47c85d5f vocab=76c9d9bf
-/
theorem inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A)
    {u : Lˣ} (hu : u ∈ A.unitGroup) :
    automorphismUnitQuotient K A (σ : decompositionGroup K A) u ∈
      A.principalUnitGroup := by
  let uA : A.unitGroup := ⟨u, hu⟩
  let eA : A ≃+* A :=
    MulSemiringAction.toRingEquiv
      (decompositionGroup K A) A (σ : decompositionGroup K A)
  let qA : A.unitGroup :=
    A.unitGroupMulEquiv.symm
      (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA) /
        A.unitGroupMulEquiv uA)
  have hres :
      Units.map (IsLocalRing.residue A).toMonoidHom
          (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA)) =
        Units.map (IsLocalRing.residue A).toMonoidHom
          (A.unitGroupMulEquiv uA) := by
    ext
    change
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv
            (decompositionGroup K A) A (σ : decompositionGroup K A)
              (A.unitGroupMulEquiv uA : A)) =
        IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)
    calc
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv
            (decompositionGroup K A) A (σ : decompositionGroup K A)
              (A.unitGroupMulEquiv uA : A)) =
          (σ : decompositionGroup K A) •
            IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) := by
        change
          IsLocalRing.residue A
              ((σ : decompositionGroup K A) •
                (A.unitGroupMulEquiv uA : A)) =
            (σ : decompositionGroup K A) •
              IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)
        exact
          IsLocalRing.ResidueField.residue_smul
            (R := A) (G := decompositionGroup K A)
            (σ : decompositionGroup K A) (A.unitGroupMulEquiv uA : A)
      _ = IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) := by
        have hσ :
            residueAction K A (σ : decompositionGroup K A) = 1 :=
          MonoidHom.mem_ker.mp σ.property
        change
          (residueAction K A (σ : decompositionGroup K A))
              (IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)) =
            IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)
        rw [hσ]
        rfl
  have hq : (qA : Lˣ) ∈ A.principalUnitGroup := by
    rw [A.coe_mem_principalUnitGroup_iff (x := qA)]
    rw [MonoidHom.mem_ker]
    change
      Units.map (IsLocalRing.residue A).toMonoidHom
          (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA) /
            A.unitGroupMulEquiv uA) = 1
    rw [map_div, hres]
    simp only [div_eq_mul_inv, mul_inv_cancel]
  have hq_coe :
      (qA : Lˣ) =
        automorphismUnitQuotient K A (σ : decompositionGroup K A) u := by
    ext
    rfl
  rw [← hq_coe]
  exact hq

/-- Prime-decomposition statement:
for `σ ∈ I_w`, the class of `σ x / x` modulo principal units.  This is the
raw class from which the character `χ_σ` is assembled after quotienting the
value group.-/
abbrev inertiaUnitQuotientClass
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (x : Lˣ) :
    Lˣ ⧸ A.principalUnitGroup :=
  QuotientGroup.mk
    (automorphismUnitQuotient K A (σ : decompositionGroup K A) x)

/-- States the theorem `inertiaUnitQuotientClass_eq_one_iff`.
@isnad1 id=iff.0h5v.s12.ee5be68b84ef from=translated src=- shape=bf3eb95a vocab=df817aa9
-/
@[simp] theorem inertiaUnitQuotientClass_eq_one_iff
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (x : Lˣ) :
    inertiaUnitQuotientClass K A σ x = 1 ↔
      automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
        A.principalUnitGroup :=
  QuotientGroup.eq_one_iff _

/-- Valuation-ring units map to the trivial raw class.
@isnad1 id=eq.1h5v.s11.104198f795ff from=translated src=- shape=37caafde vocab=21d2f42e
-/
theorem inertiaUnitQuotientClass_eq_one_of_mem_unitGroup
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A)
    {u : Lˣ} (hu : u ∈ A.unitGroup) :
    inertiaUnitQuotientClass K A σ u = 1 :=
  (inertiaUnitQuotientClass_eq_one_iff (K := K) A σ u).mpr
    (inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
      (K := K) A σ hu)

/-- The quotient map `Lˣ/U^1 -> Lˣ/Aˣ`.  It measures the remaining value
class of a raw residue-unit quotient.-/
def principalUnitQuotientToValueClass
    (A : _root_.ValuationSubring L) :
    Lˣ ⧸ A.principalUnitGroup →* Lˣ ⧸ A.unitGroup :=
  QuotientGroup.map A.principalUnitGroup A.unitGroup
    (MonoidHom.id Lˣ)
    (by
      intro x hx
      exact A.principal_units_le_units hx)

/-- States the theorem `principalUnitQuotientToValueClass_mk`.
@isnad1 id=eq.0h3v.s11.56433ca39e3f from=translated src=- shape=d6f78f85 vocab=5c722824
-/
@[simp] theorem principalUnitQuotientToValueClass_mk
    (A : _root_.ValuationSubring L) (x : Lˣ) :
    principalUnitQuotientToValueClass A
        (QuotientGroup.mk' A.principalUnitGroup x) =
      QuotientGroup.mk' A.unitGroup x :=
  rfl

/-- The value displacement of a decomposition-group automorphism at `x`.  It
is the class of `σ x / x` in the value-class quotient `Lˣ/Aˣ`.-/
abbrev valueDisplacementClass
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (x : Lˣ) :
    Lˣ ⧸ A.unitGroup :=
  QuotientGroup.mk' A.unitGroup (automorphismUnitQuotient K A σ x)

/-- States the theorem `valueDisplacementClass_eq_one_iff`.
@isnad1 id=iff.0h5v.s9.5f2ae22cfcd6 from=translated src=- shape=68ff3ab8 vocab=5ef481d8
-/
@[simp] theorem valueDisplacementClass_eq_one_iff
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (x : Lˣ) :
    valueDisplacementClass K A σ x = 1 ↔
      automorphismUnitQuotient K A σ x ∈ A.unitGroup :=
  QuotientGroup.eq_one_iff _

/-- States the theorem `principalUnitQuotientToValueClass_inertiaUnitQuotientClass`.
@isnad1 id=eq.0h5v.s12.ad6c5536967b from=translated src=- shape=517b3018 vocab=fe5d1258
-/
@[simp] theorem principalUnitQuotientToValueClass_inertiaUnitQuotientClass
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (x : Lˣ) :
    principalUnitQuotientToValueClass A
        (inertiaUnitQuotientClass K A σ x) =
      valueDisplacementClass K A (σ : decompositionGroup K A) x :=
  rfl

/-- For fixed `σ`, value displacement is a group homomorphism on `Lˣ`.-/
def valueDisplacementHom
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) :
    Lˣ →* Lˣ ⧸ A.unitGroup where
  toFun x := valueDisplacementClass K A σ x
  map_one' := by
    rw [valueDisplacementClass_eq_one_iff,
      automorphismUnitQuotient_one_arg]
    exact A.unitGroup.one_mem
  map_mul' x y := by
    change
      QuotientGroup.mk' A.unitGroup
          (automorphismUnitQuotient K A σ (x * y)) =
        QuotientGroup.mk' A.unitGroup
            (automorphismUnitQuotient K A σ x) *
          QuotientGroup.mk' A.unitGroup
            (automorphismUnitQuotient K A σ y)
    rw [automorphismUnitQuotient_mul_arg]
    exact map_mul (QuotientGroup.mk' A.unitGroup)
      (automorphismUnitQuotient K A σ x)
      (automorphismUnitQuotient K A σ y)

/-- States the theorem `valueDisplacementHom_apply`.
@isnad1 id=eq.0h5v.s10.ab72c3143e74 from=translated src=- shape=4bf5819e vocab=794eab3f
-/
@[simp] theorem valueDisplacementHom_apply
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (x : Lˣ) :
    valueDisplacementHom K A σ x =
      valueDisplacementClass K A σ x :=
  rfl

/-- In the valuation-subring model, the inertia elements whose value
displacement is trivial.  For the chosen-valuation decomposition group
this condition is automatic; for mathlib's stabilizer of the valuation subring
it is the exact source needed to turn the raw `Lˣ/U^1` class into a residue
field unit.-/
def valueTrivialInertiaGroup
    (A : _root_.ValuationSubring L) :
    Subgroup (inertiaGroup K A) where
  carrier :=
    {σ | ∀ x : Lˣ,
      valueDisplacementClass K A (σ : decompositionGroup K A) x = 1}
  one_mem' := by
    intro x
    rw [valueDisplacementClass_eq_one_iff,
      show ((1 : inertiaGroup K A) : decompositionGroup K A) = 1 by rfl,
      automorphismUnitQuotient_one]
    exact A.unitGroup.one_mem
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [valueDisplacementClass_eq_one_iff]
    rw [show
      ((σ * τ : inertiaGroup K A) : decompositionGroup K A) =
        (σ : decompositionGroup K A) * (τ : decompositionGroup K A) by rfl]
    rw [automorphismUnitQuotient_mul]
    exact A.unitGroup.mul_mem
      ((valueDisplacementClass_eq_one_iff (K := K) A
          (σ : decompositionGroup K A)
          (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv)
            x)).mp
        (hσ _))
      ((valueDisplacementClass_eq_one_iff (K := K) A
          (τ : decompositionGroup K A) x).mp
        (hτ x))
  inv_mem' := by
    intro σ hσ x
    rw [valueDisplacementClass_eq_one_iff]
    let y : Lˣ :=
      (Units.mapEquiv
        ((((σ : inertiaGroup K A)⁻¹ : inertiaGroup K A) :
          decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x
    have hy :
        automorphismUnitQuotient K A (σ : decompositionGroup K A) y ∈
          A.unitGroup :=
      (valueDisplacementClass_eq_one_iff (K := K) A
        (σ : decompositionGroup K A) y).mp (hσ y)
    have hquot :
        automorphismUnitQuotient K A
            ((σ⁻¹ : inertiaGroup K A) : decompositionGroup K A) x =
          (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ := by
      ext
      simp [automorphismUnitQuotient, y, div_eq_mul_inv]
    rw [hquot]
    exact A.unitGroup.inv_mem hy

/-- For a value-trivial inertia element, the quotient `σ x / x` is an actual
unit of the valuation ring.-/
def valueTrivialAutomorphismUnit
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    A.unitGroup :=
  ⟨automorphismUnitQuotient K A
      ((σ : inertiaGroup K A) : decompositionGroup K A) x,
    (valueDisplacementClass_eq_one_iff (K := K) A
      ((σ : inertiaGroup K A) : decompositionGroup K A) x).mp
      (σ.property x)⟩

/-- States the theorem `valueTrivialAutomorphismUnit_coe`.
@isnad1 id=eq.0h5v.s14.2aa759daaf90 from=translated src=- shape=1afcc8f8 vocab=fd79c81a
-/
@[simp] theorem valueTrivialAutomorphismUnit_coe
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    (valueTrivialAutomorphismUnit K A σ x : Lˣ) =
      automorphismUnitQuotient K A
        ((σ : inertiaGroup K A) : decompositionGroup K A) x :=
  rfl

/-- States the theorem `valueTrivialAutomorphismUnit_one_arg`.
@isnad1 id=eq.0h4v.s13.2a06e289cfa1 from=translated src=- shape=dab7d1ca vocab=4d35f05f
-/
@[simp] theorem valueTrivialAutomorphismUnit_one_arg
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    valueTrivialAutomorphismUnit K A σ 1 = 1 := by
  ext
  simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_one_arg]

/-- States the theorem `valueTrivialAutomorphismUnit_mul_arg`.
@isnad1 id=eq.0h6v.s13.592c7cf2e35e from=translated src=- shape=c2ac3109 vocab=c1f99403
-/
theorem valueTrivialAutomorphismUnit_mul_arg
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x y : Lˣ) :
    valueTrivialAutomorphismUnit K A σ (x * y) =
      valueTrivialAutomorphismUnit K A σ x *
        valueTrivialAutomorphismUnit K A σ y := by
  ext
  simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_mul_arg]

/-- The character `χ_σ` is defined by:
for value-trivial inertia, `x ↦ σ x / x mod P` is a homomorphism
`Lˣ -> λˣ`.-/
def valueTrivialInertiaResidueUnitHom
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    Lˣ →* (IsLocalRing.ResidueField A)ˣ where
  toFun x :=
    A.unitGroupToResidueFieldUnits
      (valueTrivialAutomorphismUnit K A σ x)
  map_one' := by
    rw [valueTrivialAutomorphismUnit_one_arg]
    exact map_one A.unitGroupToResidueFieldUnits
  map_mul' x y := by
    rw [valueTrivialAutomorphismUnit_mul_arg]
    exact map_mul A.unitGroupToResidueFieldUnits
      (valueTrivialAutomorphismUnit K A σ x)
      (valueTrivialAutomorphismUnit K A σ y)

/-- States the theorem `valueTrivialInertiaResidueUnitHom_apply`.
@isnad1 id=eq.0h5v.s14.c118918356ea from=translated src=- shape=9792af01 vocab=bfbce4ec
-/
@[simp] theorem valueTrivialInertiaResidueUnitHom_apply
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A σ x =
      A.unitGroupToResidueFieldUnits
        (valueTrivialAutomorphismUnit K A σ x) :=
  rfl

/-- Valuation-ring units are killed by the residue-unit character.
@isnad1 id=le.0h4v.s13.599c397ac680 from=translated src=- shape=b405133c vocab=ab5b9cc4
-/
theorem unitGroup_le_valueTrivialInertiaResidueUnitHom_ker
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    A.unitGroup ≤ (valueTrivialInertiaResidueUnitHom K A σ).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, valueTrivialInertiaResidueUnitHom_apply]
  let uA : A.unitGroup := valueTrivialAutomorphismUnit K A σ u
  have hprincipal :
      automorphismUnitQuotient K A
          ((σ : inertiaGroup K A) : decompositionGroup K A) u ∈
        A.principalUnitGroup :=
    inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
      (K := K) A (σ : inertiaGroup K A) hu
  have hker : uA ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [A.ker_unitGroupToResidueFieldUnits]
    change (uA : Lˣ) ∈ A.principalUnitGroup
    simpa [uA, valueTrivialAutomorphismUnit] using hprincipal
  change A.unitGroupToResidueFieldUnits uA = 1
  exact MonoidHom.mem_ker.mp hker

/-- Base-field units are killed by the residue-unit character.
@isnad1 id=eq.0h5v.s13.26107753c7d9 from=translated src=- shape=14d25a4d vocab=1f527de1
-/
theorem valueTrivialInertiaResidueUnitHom_baseUnit
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (a : Kˣ) :
    valueTrivialInertiaResidueUnitHom K A σ
        (Units.map (algebraMap K L).toMonoidHom a) = 1 := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  let uA : A.unitGroup :=
    valueTrivialAutomorphismUnit K A σ
      (Units.map (algebraMap K L).toMonoidHom a)
  have hprincipal :
      automorphismUnitQuotient K A
          ((σ : inertiaGroup K A) : decompositionGroup K A)
          (Units.map (algebraMap K L).toMonoidHom a) ∈
        A.principalUnitGroup := by
    rw [automorphismUnitQuotient_algebraMapUnit]
    exact A.principalUnitGroup.one_mem
  have hker : uA ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [A.ker_unitGroupToResidueFieldUnits]
    change (uA : Lˣ) ∈ A.principalUnitGroup
    simpa [uA, valueTrivialAutomorphismUnit] using hprincipal
  change A.unitGroupToResidueFieldUnits uA = 1
  exact MonoidHom.mem_ker.mp hker

/-- A value-trivial inertia element changes a unit representative only by a
valuation-ring unit, hence every residue-unit character is unchanged after
applying it to the representative.
@isnad1 id=eq.0h6v.s15.cdcf389da807 from=translated src=- shape=f45e4ba1 vocab=2f0bf9d7
-/
theorem valueTrivialInertiaResidueUnitHom_mapEquiv_arg
    (A : _root_.ValuationSubring L)
    (σ τ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A σ
        (Units.mapEquiv
          ((((τ : inertiaGroup K A) : decompositionGroup K A) :
            L ≃ₐ[K] L).toMulEquiv) x) =
      valueTrivialInertiaResidueUnitHom K A σ x := by
  let q : Lˣ :=
    automorphismUnitQuotient K A
      ((τ : inertiaGroup K A) : decompositionGroup K A) x
  have hq_mem : q ∈ A.unitGroup :=
    (valueDisplacementClass_eq_one_iff (K := K) A
      ((τ : inertiaGroup K A) : decompositionGroup K A) x).mp
      (τ.property x)
  have harg :
      Units.mapEquiv
          ((((τ : inertiaGroup K A) : decompositionGroup K A) :
            L ≃ₐ[K] L).toMulEquiv) x =
        q * x := by
    ext
    simp [q, automorphismUnitQuotient, div_eq_mul_inv, mul_comm]
  rw [harg, map_mul]
  have hq :
      valueTrivialInertiaResidueUnitHom K A σ q = 1 :=
    MonoidHom.mem_ker.mp
      (unitGroup_le_valueTrivialInertiaResidueUnitHom_ker
        (K := K) A σ hq_mem)
  rw [hq, one_mul]

/-- The identity inertia element gives the trivial residue-unit character.
@isnad1 id=eq.0h4v.s14.fe73c4dc81e7 from=translated src=- shape=78c6e6be vocab=20d4af1c
-/
theorem valueTrivialInertiaResidueUnitHom_one
    (A : _root_.ValuationSubring L) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A
        (1 : valueTrivialInertiaGroup K A) x = 1 := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  have hunit :
      valueTrivialAutomorphismUnit K A
          (1 : valueTrivialInertiaGroup K A) x = 1 := by
    ext
    simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_one]
  rw [hunit]
  exact map_one A.unitGroupToResidueFieldUnits

/-- Prime-decomposition statement:
the residue-unit characters multiply with the inertia element.
@isnad1 id=eq.0h6v.s16.cd51489b1ec7 from=translated src=- shape=984f194b vocab=5587da99
-/
theorem valueTrivialInertiaResidueUnitHom_mul
    (A : _root_.ValuationSubring L)
    (σ τ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A (σ * τ) x =
      valueTrivialInertiaResidueUnitHom K A σ x *
        valueTrivialInertiaResidueUnitHom K A τ x := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  have hunit :
      valueTrivialAutomorphismUnit K A (σ * τ) x =
        valueTrivialAutomorphismUnit K A σ
          (Units.mapEquiv
            ((((τ : inertiaGroup K A) : decompositionGroup K A) :
              L ≃ₐ[K] L).toMulEquiv) x) *
        valueTrivialAutomorphismUnit K A τ x := by
    ext
    simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_mul]
  rw [hunit, map_mul]
  change
    valueTrivialInertiaResidueUnitHom K A σ
        (Units.mapEquiv
          ((((τ : inertiaGroup K A) : decompositionGroup K A) :
            L ≃ₐ[K] L).toMulEquiv) x) *
      valueTrivialInertiaResidueUnitHom K A τ x =
    valueTrivialInertiaResidueUnitHom K A σ x *
      valueTrivialInertiaResidueUnitHom K A τ x
  rw [valueTrivialInertiaResidueUnitHom_mapEquiv_arg]

/-- Prime-decomposition statement:
the residue-unit character descends from representatives `x : Lˣ` to value
classes modulo valuation-ring units.-/
def valueClassToResidueUnits
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    Lˣ ⧸ A.unitGroup →* (IsLocalRing.ResidueField A)ˣ :=
  QuotientGroup.lift A.unitGroup
    (valueTrivialInertiaResidueUnitHom K A σ)
    (unitGroup_le_valueTrivialInertiaResidueUnitHom_ker (K := K) A σ)

/-- States the theorem `valueClassToResidueUnits_mk`.
@isnad1 id=eq.0h5v.s14.14a7cf93049e from=translated src=- shape=ec921082 vocab=861ceb52
-/
@[simp] theorem valueClassToResidueUnits_mk
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueClassToResidueUnits K A σ
        (QuotientGroup.mk' A.unitGroup x) =
      valueTrivialInertiaResidueUnitHom K A σ x :=
  rfl

/-- States the theorem `valueTrivialInertiaResidueUnitHom_eq_one_of_mem_ramificationGroup`.
@isnad1 id=eq.1h5v.s15.c6a529afa732 from=translated src=- shape=6831e756 vocab=53677c28
-/
theorem valueTrivialInertiaResidueUnitHom_eq_one_of_mem_ramificationGroup
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
    (hσ : (σ : inertiaGroup K A) ∈ ramificationGroup K A)
    (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A σ x = 1 := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  let uA : A.unitGroup := valueTrivialAutomorphismUnit K A σ x
  have hprincipal :
      automorphismUnitQuotient K A
          ((σ : inertiaGroup K A) : decompositionGroup K A) x ∈
        A.principalUnitGroup :=
    (mem_ramificationGroup_iff (K := K) A (σ : inertiaGroup K A)).mp hσ x
  have hker : uA ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [A.ker_unitGroupToResidueFieldUnits]
    change (uA : Lˣ) ∈ A.principalUnitGroup
    simpa [uA, valueTrivialAutomorphismUnit] using hprincipal
  change A.unitGroupToResidueFieldUnits uA = 1
  exact MonoidHom.mem_ker.mp hker

/-- Prime-decomposition statement:
for fixed `σ ∈ I_w`, the raw unit quotient is a group homomorphism
`Lˣ -> Lˣ / U^1`.-/
def inertiaUnitQuotientHom
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    Lˣ →* Lˣ ⧸ A.principalUnitGroup where
  toFun x := inertiaUnitQuotientClass K A σ x
  map_one' := by
    rw [inertiaUnitQuotientClass_eq_one_iff,
      automorphismUnitQuotient_one_arg]
    exact A.principalUnitGroup.one_mem
  map_mul' x y := by
    change
      QuotientGroup.mk' A.principalUnitGroup
          (automorphismUnitQuotient K A
            (σ : decompositionGroup K A) (x * y)) =
        QuotientGroup.mk' A.principalUnitGroup
            (automorphismUnitQuotient K A
              (σ : decompositionGroup K A) x) *
          QuotientGroup.mk' A.principalUnitGroup
            (automorphismUnitQuotient K A
              (σ : decompositionGroup K A) y)
    rw [automorphismUnitQuotient_mul_arg]
    exact map_mul (QuotientGroup.mk' A.principalUnitGroup)
      (automorphismUnitQuotient K A (σ : decompositionGroup K A) x)
      (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)

/-- States the theorem `inertiaUnitQuotientHom_apply`.
@isnad1 id=eq.0h5v.s11.8a2e73cb5e05 from=translated src=- shape=d2c5a11e vocab=4a190d98
-/
@[simp] theorem inertiaUnitQuotientHom_apply
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (x : Lˣ) :
    inertiaUnitQuotientHom K A σ x =
      inertiaUnitQuotientClass K A σ x :=
  rfl

/-- The raw quotient homomorphism kills the valuation-ring unit group.
@isnad1 id=le.0h4v.s11.d013d509b0d3 from=translated src=- shape=1b58b2f2 vocab=fcc0b24b
-/
theorem unitGroup_le_inertiaUnitQuotientHom_ker
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    A.unitGroup ≤ (inertiaUnitQuotientHom K A σ).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, inertiaUnitQuotientHom_apply]
  exact inertiaUnitQuotientClass_eq_one_of_mem_unitGroup (K := K) A σ hu

/-- Prime-decomposition statement:
the raw character descends from representatives `x : Lˣ` to value classes
modulo valuation-ring units.  This is the quotient layer corresponding to
`Delta = w(L*)`.-/
def valueClassToPrincipalUnitQuotient
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    Lˣ ⧸ A.unitGroup →* Lˣ ⧸ A.principalUnitGroup :=
  QuotientGroup.lift A.unitGroup
    (inertiaUnitQuotientHom K A σ)
    (unitGroup_le_inertiaUnitQuotientHom_ker (K := K) A σ)

/-- States the theorem `valueClassToPrincipalUnitQuotient_mk`.
@isnad1 id=eq.0h5v.s12.6c4e3c5415d6 from=translated src=- shape=bad04679 vocab=b8226194
-/
@[simp] theorem valueClassToPrincipalUnitQuotient_mk
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (x : Lˣ) :
    valueClassToPrincipalUnitQuotient K A σ
        (QuotientGroup.mk' A.unitGroup x) =
      inertiaUnitQuotientClass K A σ x :=
  rfl

/-- The image of base-field units in `Lˣ / A.unitGroup`.  This is the
subgroup that later realizes `Gamma` inside `Delta`.-/
def baseUnitToValueClass (A : _root_.ValuationSubring L) :
    Kˣ →* Lˣ ⧸ A.unitGroup :=
  (QuotientGroup.mk' A.unitGroup).comp
    (Units.map (algebraMap K L).toMonoidHom)

/-- States the theorem `baseUnitToValueClass_apply`.
@isnad1 id=eq.0h4v.s11.8ea4c86a9121 from=translated src=- shape=11fd3b9c vocab=81bda725
-/
@[simp] theorem baseUnitToValueClass_apply
    (A : _root_.ValuationSubring L) (a : Kˣ) :
    baseUnitToValueClass K A a =
      QuotientGroup.mk' A.unitGroup
        (Units.map (algebraMap K L).toMonoidHom a) :=
  rfl

/-- The subgroup of `Lˣ/A.unitGroup` generated by base-field value classes.-/
abbrev baseUnitValueClassSubgroup (A : _root_.ValuationSubring L) :
    Subgroup (Lˣ ⧸ A.unitGroup) :=
  (baseUnitToValueClass K A).range

/-- Provides the instance `baseUnitValueClassSubgroup_normal`.
@isnad1 id=normal.0h3v.s7.f573e1433e91 from=translated src=- shape=16c22842 vocab=ff537ea7
-/
instance baseUnitValueClassSubgroup_normal
    (A : _root_.ValuationSubring L) :
    (baseUnitValueClassSubgroup K A).Normal :=
  ⟨by
    intro n hn g
    have hconj : g * n * g⁻¹ = n := by
      rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn⟩

/-- Base-field units map trivially under the descended raw character.
@isnad1 id=eq.0h5v.s12.8997363cc61e from=translated src=- shape=c2dd0c8d vocab=2e5d638a
-/
theorem valueClassToPrincipalUnitQuotient_baseUnit
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (a : Kˣ) :
    valueClassToPrincipalUnitQuotient K A σ
        (baseUnitToValueClass K A a) = 1 := by
  rw [baseUnitToValueClass_apply, valueClassToPrincipalUnitQuotient_mk]
  exact (inertiaUnitQuotientClass_eq_one_iff
    (K := K) A σ (Units.map (algebraMap K L).toMonoidHom a)).mpr (by
      rw [automorphismUnitQuotient_algebraMapUnit]
      exact A.principalUnitGroup.one_mem)

/-- The base-field value classes lie in the kernel of the descended raw
character.
@isnad1 id=le.0h4v.s11.c3e3f473a40a from=translated src=- shape=3bcf4ac6 vocab=5c9a911b
-/
theorem baseUnitValueClassSubgroup_le_valueClassToPrincipalUnitQuotient_ker
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    baseUnitValueClassSubgroup K A ≤
      (valueClassToPrincipalUnitQuotient K A σ).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker]
  exact valueClassToPrincipalUnitQuotient_baseUnit (K := K) A σ a

/-- Prime-decomposition statement:
the raw character descends further modulo the base value group.  This quotient
is the group-theoretic model of `Delta/Gamma` before identifying it with a
concrete value-group quotient.-/
def valueModuloBaseToPrincipalUnitQuotient
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    (Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
      Lˣ ⧸ A.principalUnitGroup :=
  QuotientGroup.lift (baseUnitValueClassSubgroup K A)
    (valueClassToPrincipalUnitQuotient K A σ)
    (baseUnitValueClassSubgroup_le_valueClassToPrincipalUnitQuotient_ker
      (K := K) A σ)

/-- States the theorem `valueModuloBaseToPrincipalUnitQuotient_mk`.
@isnad1 id=eq.0h5v.s13.633c28cecde8 from=translated src=- shape=d99937c3 vocab=d75997e5
-/
@[simp] theorem valueModuloBaseToPrincipalUnitQuotient_mk
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A)
    (x : Lˣ ⧸ A.unitGroup) :
    valueModuloBaseToPrincipalUnitQuotient K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A) x) =
      valueClassToPrincipalUnitQuotient K A σ x :=
  rfl

/-- States the theorem `valueModuloBaseToPrincipalUnitQuotient_mk_mk`.
@isnad1 id=eq.0h5v.s13.9c8da1e57e28 from=translated src=- shape=51b23ec7 vocab=4efb0ae0
-/
@[simp] theorem valueModuloBaseToPrincipalUnitQuotient_mk_mk
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) (x : Lˣ) :
    valueModuloBaseToPrincipalUnitQuotient K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
          (QuotientGroup.mk' A.unitGroup x)) =
      inertiaUnitQuotientClass K A σ x :=
  rfl

/-- The base value classes are killed by the residue-unit character.
@isnad1 id=le.0h4v.s13.02ee1c5d64b2 from=translated src=- shape=a45835db vocab=a3d60973
-/
theorem baseUnitValueClassSubgroup_le_valueClassToResidueUnits_ker
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    baseUnitValueClassSubgroup K A ≤
      (valueClassToResidueUnits K A σ).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, baseUnitToValueClass_apply,
    valueClassToResidueUnits_mk]
  exact valueTrivialInertiaResidueUnitHom_baseUnit (K := K) A σ a

/-- Prime-decomposition statement:
the residue-unit character on `Delta/Gamma`, modeled as
`(Lˣ/Aˣ)/(Kˣ)`, for value-trivial inertia.-/
def valueModuloBaseToResidueUnits
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    (Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
      (IsLocalRing.ResidueField A)ˣ :=
  QuotientGroup.lift (baseUnitValueClassSubgroup K A)
    (valueClassToResidueUnits K A σ)
    (baseUnitValueClassSubgroup_le_valueClassToResidueUnits_ker
      (K := K) A σ)

/-- States the theorem `valueModuloBaseToResidueUnits_mk`.
@isnad1 id=eq.0h5v.s14.e17969266f89 from=translated src=- shape=115caf53 vocab=877325f9
-/
@[simp] theorem valueModuloBaseToResidueUnits_mk
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ ⧸ A.unitGroup) :
    valueModuloBaseToResidueUnits K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A) x) =
      valueClassToResidueUnits K A σ x :=
  rfl

/-- States the theorem `valueModuloBaseToResidueUnits_mk_mk`.
@isnad1 id=eq.0h5v.s14.da5d18ef4af0 from=translated src=- shape=093552da vocab=609e672d
-/
@[simp] theorem valueModuloBaseToResidueUnits_mk_mk
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueModuloBaseToResidueUnits K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
          (QuotientGroup.mk' A.unitGroup x)) =
      valueTrivialInertiaResidueUnitHom K A σ x :=
  rfl

/-- The inertia-character construction satisfies:
an element of `R_w` gives the trivial residue-unit character on
`Delta/Gamma`.  This is the kernel direction for the canonical map from
inertia to `Hom(Delta/Gamma, lambda*)`.
@isnad1 id=eq.1h4v.s15.b6e67a75d0b1 from=translated src=- shape=43c06420 vocab=6b16b162
-/
theorem valueModuloBaseToResidueUnits_eq_one_of_mem_ramificationGroup
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
    (hσ : (σ : inertiaGroup K A) ∈ ramificationGroup K A) :
    valueModuloBaseToResidueUnits K A σ = 1 := by
  apply QuotientGroup.monoidHom_ext
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply,
    valueModuloBaseToResidueUnits_mk_mk,
    MonoidHom.one_apply]
  simpa using valueTrivialInertiaResidueUnitHom_eq_one_of_mem_ramificationGroup
    (K := K) A σ hσ x

/-- prime-decomposition theory:
`σ ↦ χ_σ`, realized on the group-theoretic model of `Delta/Gamma`.

For mathlib's valuation-subring stabilizer this is stated on the value-trivial
inertia subgroup; for a chosen valuation in the exact-extension sense this is the
ordinary inertia group.-/
def valueTrivialInertiaCharacterHom
    (A : _root_.ValuationSubring L) :
    valueTrivialInertiaGroup K A →*
      ((Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
        (IsLocalRing.ResidueField A)ˣ) where
  toFun σ := valueModuloBaseToResidueUnits K A σ
  map_one' := by
    apply QuotientGroup.monoidHom_ext
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply,
      valueModuloBaseToResidueUnits_mk_mk,
      MonoidHom.one_apply]
    exact valueTrivialInertiaResidueUnitHom_one (K := K) A x
  map_mul' σ τ := by
    apply QuotientGroup.monoidHom_ext
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro x
    change
      valueModuloBaseToResidueUnits K A (σ * τ)
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
            (QuotientGroup.mk' A.unitGroup x)) =
        valueModuloBaseToResidueUnits K A σ
            (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
              (QuotientGroup.mk' A.unitGroup x)) *
          valueModuloBaseToResidueUnits K A τ
            (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
              (QuotientGroup.mk' A.unitGroup x))
    rw [valueModuloBaseToResidueUnits_mk_mk,
      valueModuloBaseToResidueUnits_mk_mk,
      valueModuloBaseToResidueUnits_mk_mk]
    exact valueTrivialInertiaResidueUnitHom_mul (K := K) A σ τ x

/-- States the theorem `valueTrivialInertiaCharacterHom_apply`.
@isnad1 id=eq.0h4v.s17.a12af9b1c066 from=translated src=- shape=43efffb2 vocab=e19fcc13
-/
@[simp] theorem valueTrivialInertiaCharacterHom_apply
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    valueTrivialInertiaCharacterHom K A σ =
      valueModuloBaseToResidueUnits K A σ :=
  rfl

/-- The ramification group is contained in the kernel of the character map.
@isnad1 id=mem.1h4v.s17.50a7cf9cf7c6 from=translated src=- shape=5dd7bba4 vocab=e9b4f825
-/
theorem valueTrivialInertiaCharacterHom_mem_ker_of_mem_ramificationGroup
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
    (hσ : (σ : inertiaGroup K A) ∈ ramificationGroup K A) :
    σ ∈ (valueTrivialInertiaCharacterHom K A).ker := by
  rw [MonoidHom.mem_ker, valueTrivialInertiaCharacterHom_apply]
  exact valueModuloBaseToResidueUnits_eq_one_of_mem_ramificationGroup
    (K := K) A σ hσ

/-- Conversely, a value-trivial inertia element with trivial character lies in
the ramification group.
@isnad1 id=mem.1h4v.s17.38c829b33273 from=translated src=- shape=b5f70480 vocab=e9b4f825
-/
theorem mem_ramificationGroup_of_valueTrivialInertiaCharacterHom_mem_ker
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
    (hσ : σ ∈ (valueTrivialInertiaCharacterHom K A).ker) :
    (σ : inertiaGroup K A) ∈ ramificationGroup K A := by
  rw [mem_ramificationGroup_iff]
  intro x
  have hchar :
      valueModuloBaseToResidueUnits K A σ
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
            (QuotientGroup.mk' A.unitGroup x)) = 1 := by
    have hhom :
        valueTrivialInertiaCharacterHom K A σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have happ :=
      congrArg
        (fun f :
          (Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
            (IsLocalRing.ResidueField A)ˣ =>
          f (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
            (QuotientGroup.mk' A.unitGroup x))) hhom
    simpa [valueTrivialInertiaCharacterHom_apply] using happ
  have hres :
      A.unitGroupToResidueFieldUnits
          (valueTrivialAutomorphismUnit K A σ x) = 1 := by
    rw [valueModuloBaseToResidueUnits_mk_mk] at hchar
    simpa only [valueTrivialInertiaResidueUnitHom_apply] using hchar
  have hker :
      valueTrivialAutomorphismUnit K A σ x ∈
        A.unitGroupToResidueFieldUnits.ker :=
    MonoidHom.mem_ker.mpr hres
  rw [A.ker_unitGroupToResidueFieldUnits] at hker
  have hker' :
      (valueTrivialAutomorphismUnit K A σ x : Lˣ) ∈
        A.principalUnitGroup := hker
  simpa [valueTrivialAutomorphismUnit] using hker'

/-- Prime-decomposition statement:
on value-trivial inertia, the kernel of `σ ↦ χ_σ` is exactly `R_w`.
@isnad1 id=iff.0h4v.s17.67706a26cfba from=translated src=- shape=b66aa416 vocab=e9b4f825
-/
theorem valueTrivialInertiaCharacterHom_mem_ker_iff
    (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A) :
    σ ∈ (valueTrivialInertiaCharacterHom K A).ker ↔
      (σ : inertiaGroup K A) ∈ ramificationGroup K A := by
  constructor
  · exact mem_ramificationGroup_of_valueTrivialInertiaCharacterHom_mem_ker
      (K := K) A σ
  · exact valueTrivialInertiaCharacterHom_mem_ker_of_mem_ramificationGroup
      (K := K) A σ

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
