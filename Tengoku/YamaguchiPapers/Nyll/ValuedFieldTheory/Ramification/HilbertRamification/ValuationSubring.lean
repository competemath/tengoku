/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Exact.Basic
import Tengoku.Seed.Algebra.Group.Units.Equiv
import Tengoku.Seed.Algebra.Group.Subgroup.Map
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.RingTheory.Valuation.RamificationGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert ramification theory: valuation-subring layer

This file manages the ordinary valuation-subring decomposition/inertia exact
sequence.  For an arbitrary valuation subring the residue action need not be
onto the full residue automorphism group; the canonical theorem is the exact
sequence with target equal to the range of the residue action.
-/

namespace RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- finite Galois ramification theory:
the decomposition group of a valuation subring.-/
abbrev decompositionGroup (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  A.decompositionSubgroup K

/-- finite Galois ramification theory:
the inertia group of a valuation subring.-/
abbrev inertiaGroup (A : _root_.ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  A.inertiaSubgroup K

/-- The residue action of the decomposition group on the residue field.-/
abbrev residueAction (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- The inertia group is the kernel of the residue action.
@isnad1 id=eq.0h3v.s11.87aa694103d9 from=translated src=- shape=9c27ee21 vocab=9d8030ad
-/
theorem residueAction_ker (A : _root_.ValuationSubring L) :
    MonoidHom.ker (residueAction K A) = inertiaGroup K A := by
  rfl

/-- Provides the instance `inertiaGroup_normal`.
@isnad1 id=normal.0h3v.s8.9861b17b1177 from=translated src=- shape=325129f1 vocab=47d5ec5d
-/
instance inertiaGroup_normal (A : _root_.ValuationSubring L) :
    (inertiaGroup K A).Normal := by
  rw [← residueAction_ker (K := K) A]
  infer_instance

/-- finite Galois ramification theory:
the unit quotient `σ x / x` attached to an automorphism in the decomposition
group.  This is the expression used in the definition of the ramification
group.-/
def automorphismUnitQuotient
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (x : Lˣ) :
    Lˣ :=
  Units.mapEquiv ((σ : L ≃ₐ[K] L).toMulEquiv) x / x

/-- States the theorem `automorphismUnitQuotient_one`.
@isnad1 id=eq.0h4v.s9.c73bc4028bd5 from=translated src=- shape=ee33b340 vocab=9415e3f6
-/
@[simp] theorem automorphismUnitQuotient_one
    (A : _root_.ValuationSubring L) (x : Lˣ) :
    automorphismUnitQuotient K A 1 x = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- States the theorem `automorphismUnitQuotient_mul`.
@isnad1 id=eq.0h6v.s11.8cc275ac1e37 from=translated src=- shape=de0b4eab vocab=6d4d0341
-/
theorem automorphismUnitQuotient_mul
    (A : _root_.ValuationSubring L) (σ τ : decompositionGroup K A) (x : Lˣ) :
    automorphismUnitQuotient K A (σ * τ) x =
      automorphismUnitQuotient K A σ
        (Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) x) *
      automorphismUnitQuotient K A τ x := by
  ext
  simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]

/-- The decomposition and inertia subgroup definitions:
the ramification group `R_w`, as the subgroup of inertia whose unit quotients
`σ x / x` are principal units for every `x : Lˣ`.-/
def ramificationGroup (A : _root_.ValuationSubring L) :
    Subgroup (inertiaGroup K A) where
  carrier :=
    {σ | ∀ x : Lˣ,
      automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
        A.principalUnitGroup}
  one_mem' := by
    intro x
    have hmap : Units.mapEquiv (AlgEquiv.toMulEquiv (1 : L ≃ₐ[K] L)) x = x := by
      ext
      rfl
    simp [automorphismUnitQuotient, hmap]
  mul_mem' := by
    intro σ τ hσ hτ x
    change
      automorphismUnitQuotient K A ((σ * τ : inertiaGroup K A) : decompositionGroup K A) x ∈
        A.principalUnitGroup
    have hx :
        automorphismUnitQuotient K A (σ : decompositionGroup K A)
            (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x) *
          automorphismUnitQuotient K A (τ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
      A.principalUnitGroup.mul_mem
      (hσ (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x))
      (hτ x)
    simpa [automorphismUnitQuotient_mul] using hx
  inv_mem' := by
    intro σ hσ x
    let y : Lˣ :=
      Units.mapEquiv
        ((((σ : decompositionGroup K A)⁻¹ : decompositionGroup K A) :
          L ≃ₐ[K] L).toMulEquiv) x
    have hy :
        automorphismUnitQuotient K A (σ : decompositionGroup K A) y ∈
          A.principalUnitGroup :=
      hσ y
    have hyinv :
        (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ ∈
          A.principalUnitGroup :=
      A.principalUnitGroup.inv_mem hy
    have hquot :
        automorphismUnitQuotient K A
            ((σ⁻¹ : inertiaGroup K A) : decompositionGroup K A) x =
          (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ := by
      ext
      simp [automorphismUnitQuotient, y, div_eq_mul_inv]
    rw [hquot]
    exact hyinv

/-- States the theorem `mem_ramificationGroup_iff`.
@isnad1 id=iff.0h4v.s13.96473d2952c2 from=translated src=- shape=b5a3a7d3 vocab=9c46ccdb
-/
@[simp] theorem mem_ramificationGroup_iff
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    σ ∈ ramificationGroup K A ↔
      ∀ x : Lˣ,
        automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
  Iff.rfl

/-- finite Galois ramification theory:
the decomposition field `Z_w` is the fixed field of the decomposition group.-/
abbrev decompositionField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup K A)

/-- States the theorem `mem_decompositionField_iff`.
@isnad1 id=iff.0h4v.s8.6e9452a6ee8c from=translated src=- shape=1a98371e vocab=64606ea0
-/
@[simp] theorem mem_decompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ decompositionField K A ↔
      ∀ σ ∈ decompositionGroup K A, σ x = x := by
  exact IntermediateField.mem_fixedField_iff
    (H := decompositionGroup K A) x

/-- The inertia group as a subgroup of the full `K`-automorphism group of `L`.
This is the subgroup whose fixed field is the classical inertia field.-/
abbrev inertiaGroupInAut (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.map (decompositionGroup K A).subtype (inertiaGroup K A)

/-- The canonical inclusion `I_w -> G(L/K)`.-/
def inertiaGroupToAut (A : _root_.ValuationSubring L) :
    inertiaGroup K A →* (L ≃ₐ[K] L) :=
  (decompositionGroup K A).subtype.comp (inertiaGroup K A).subtype

/-- States the theorem `inertiaGroupToAut_apply`.
@isnad1 id=eq.0h4v.s14.e6c847d25b74 from=translated src=- shape=833c5444 vocab=1614368f
-/
@[simp] theorem inertiaGroupToAut_apply
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    inertiaGroupToAut (K := K) A σ =
      ((σ : decompositionGroup K A) : L ≃ₐ[K] L) :=
  rfl

/-- The inertia-field definition:
the inertia field `T_w` is the fixed field of the inertia group.-/
abbrev inertiaField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (inertiaGroupInAut K A)

/-- States the theorem `mem_inertiaField_iff`.
@isnad1 id=iff.0h4v.s11.d2acebc5a5c0 from=translated src=- shape=7c029aef vocab=333ec969
-/
@[simp] theorem mem_inertiaField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ inertiaField K A ↔
      ∀ σ : inertiaGroup K A, ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [inertiaField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ
    exact h ((σ : decompositionGroup K A) : L ≃ₐ[K] L)
      ⟨(σ : decompositionGroup K A), σ.property, rfl⟩
  · intro h σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    exact h ⟨τ, hτ⟩

/-- The inertia subgroup, viewed inside the full automorphism group, lies in
the decomposition group.
@isnad1 id=le.0h3v.s7.9158adfb595a from=translated src=- shape=31712832 vocab=3c370381
-/
theorem inertiaGroupInAut_le_decompositionGroup
    (A : _root_.ValuationSubring L) :
    inertiaGroupInAut K A ≤ decompositionGroup K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact τ.property

/-- The ramification group as a subgroup of the full automorphism group.-/
abbrev ramificationGroupInAut (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.map (inertiaGroupToAut (K := K) A) (ramificationGroup K A)

/-- The ramification-field definition:
the ramification field `V_w` is the fixed field of the ramification group.-/
abbrev ramificationField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (ramificationGroupInAut K A)

/-- States the theorem `mem_ramificationField_iff`.
@isnad1 id=iff.0h4v.s14.5e625e7e88c8 from=translated src=- shape=df90344d vocab=d87a9a7e
-/
@[simp] theorem mem_ramificationField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ ramificationField K A ↔
      ∀ σ : ramificationGroup K A,
        (((σ : inertiaGroup K A) : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [ramificationField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ
    exact h (inertiaGroupToAut (K := K) A (σ : inertiaGroup K A))
      ⟨(σ : inertiaGroup K A), σ.property, rfl⟩
  · intro h σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    exact h ⟨τ, hτ⟩

/-- The ramification subgroup, viewed in `G(L/K)`, lies in inertia.
@isnad1 id=le.0h3v.s7.1a0c638a16dc from=translated src=- shape=31712832 vocab=6257ca58
-/
theorem ramificationGroupInAut_le_inertiaGroupInAut
    (A : _root_.ValuationSubring L) :
    ramificationGroupInAut K A ≤ inertiaGroupInAut K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩

/-- finite Galois ramification theory:
the inertia field is contained in the ramification field.
@isnad1 id=le.0h3v.s6.61ac7de7d76e from=translated src=- shape=d02e1986 vocab=c7e1d905
-/
theorem inertiaField_le_ramificationField
    (A : _root_.ValuationSubring L) :
    inertiaField K A ≤ ramificationField K A :=
  IntermediateField.fixedField_le
    (ramificationGroupInAut_le_inertiaGroupInAut (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the inertia field
`T_w`.-/
abbrev ramificationFieldOverInertiaField
    (A : _root_.ValuationSubring L) :
    IntermediateField (inertiaField K A) L :=
  IntermediateField.extendScalars
    (inertiaField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverInertiaField_restrictScalars`.
@isnad1 id=eq.0h3v.s7.9893c7592636 from=translated src=- shape=05075ce9 vocab=3991369c
-/
@[simp] theorem ramificationFieldOverInertiaField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (ramificationFieldOverInertiaField K A).restrictScalars K =
      ramificationField K A :=
  rfl

/-- The ramification group is canonically equivalent to its image in
`G(L/K)`.-/
def ramificationGroupEquivInAut
    (A : _root_.ValuationSubring L) :
    ramificationGroup K A ≃* ramificationGroupInAut K A :=
  (ramificationGroup K A).equivMapOfInjective
    (inertiaGroupToAut (K := K) A)
    (by
      intro σ τ h
      apply Subtype.ext
      apply Subtype.ext
      simpa [inertiaGroupToAut] using h)

/-- The ramification-field definition source:
the ramification group is the Galois group over its fixed field.-/
def ramificationGroupEquivGalRamificationField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    ramificationGroup K A ≃* (L ≃ₐ[ramificationField K A] L) :=
  (ramificationGroupEquivInAut (K := K) A).trans
    (IntermediateField.subgroupEquivAlgEquiv (ramificationGroupInAut K A))

/-- finite Galois ramification theory:
the decomposition field is contained in the inertia field.
@isnad1 id=le.0h3v.s6.849cf94a04c8 from=translated src=- shape=d02e1986 vocab=8e14754f
-/
theorem decompositionField_le_inertiaField
    (A : _root_.ValuationSubring L) :
    decompositionField K A ≤ inertiaField K A :=
  IntermediateField.fixedField_le
    (inertiaGroupInAut_le_decompositionGroup (K := K) A)

/-- finite Galois ramification theory:
the decomposition field is contained in the ramification field.
@isnad1 id=le.0h3v.s6.d19ceccfccf0 from=translated src=- shape=d02e1986 vocab=d1fbfaef
-/
theorem decompositionField_le_ramificationField
    (A : _root_.ValuationSubring L) :
    decompositionField K A ≤ ramificationField K A :=
  (decompositionField_le_inertiaField (K := K) A).trans
    (inertiaField_le_ramificationField (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `V_w | Z_w`.-/
abbrev ramificationFieldOverDecompositionField
    (A : _root_.ValuationSubring L) :
    IntermediateField (decompositionField K A) L :=
  IntermediateField.extendScalars
    (decompositionField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverDecompositionField_restrictScalars`.
@isnad1 id=eq.0h3v.s7.97983c25c567 from=translated src=- shape=05075ce9 vocab=1134c7fe
-/
@[simp] theorem ramificationFieldOverDecompositionField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (ramificationFieldOverDecompositionField K A).restrictScalars K =
      ramificationField K A :=
  rfl

/-- The inertia-field definition source:
the inertia field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `G(T_w/Z_w)`.-/
abbrev inertiaFieldOverDecompositionField
    (A : _root_.ValuationSubring L) :
    IntermediateField (decompositionField K A) L :=
  IntermediateField.extendScalars
    (decompositionField_le_inertiaField (K := K) A)

/-- States the theorem `mem_inertiaFieldOverDecompositionField_iff`.
@isnad1 id=iff.0h4v.s12.00224f400ad5 from=translated src=- shape=3cf2fdd5 vocab=4f59d791
-/
@[simp] theorem mem_inertiaFieldOverDecompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ inertiaFieldOverDecompositionField K A ↔
      ∀ σ : inertiaGroup K A, ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [inertiaFieldOverDecompositionField, IntermediateField.mem_extendScalars,
    mem_inertiaField_iff]

/-- States the theorem `inertiaFieldOverDecompositionField_restrictScalars`.
@isnad1 id=eq.0h3v.s7.c37d450f2ce1 from=translated src=- shape=05075ce9 vocab=ce3aa72e
-/
@[simp] theorem inertiaFieldOverDecompositionField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (inertiaFieldOverDecompositionField K A).restrictScalars K =
      inertiaField K A :=
  rfl

/-- The fixed-field description of decomposition source:
the decomposition group is the Galois group over its fixed field.-/
def decompositionGroupEquivGalDecompositionField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    decompositionGroup K A ≃* (L ≃ₐ[decompositionField K A] L) :=
  IntermediateField.subgroupEquivAlgEquiv (decompositionGroup K A)

/-- The fixed-field description of decomposition source:
`L/Z_w` is Galois because `Z_w` is the fixed field of the finite
decomposition group action.
@isnad1 id=isgalois.0h3v.s7.63f7a891f50a from=translated src=- shape=28e96abd vocab=4a0d0193
-/
instance decompositionField_isGalois
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IsGalois (decompositionField K A) L :=
  IsGalois.of_fixed_field L (decompositionGroup K A)

/--
States the theorem `decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply`.
@isnad1 id=eq.0h5v.s12.9a6672f8d7d1 from=translated src=- shape=7985af98 vocab=00349bff
-/
@[simp] theorem decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : decompositionGroup K A) (x : L) :
    decompositionGroupEquivGalDecompositionField_of_finiteDimensional (K := K) A σ x =
      ((σ : L ≃ₐ[K] L) x) :=
  rfl

/-- The inertia-field definition source:
the inertia subgroup transported to `Gal(L/Z_w)` through
`G_w = G(L/Z_w)`.-/
abbrev inertiaGroupOverDecompositionField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[decompositionField K A] L) :=
  Subgroup.map
    (decompositionGroupEquivGalDecompositionField_of_finiteDimensional
      (K := K) A).toMonoidHom
    (inertiaGroup K A)

/-- States the theorem `mem_inertiaGroupOverDecompositionField_iff`.
@isnad1 id=iff.0h4v.s13.e4a7666df1f9 from=translated src=- shape=6cbe93ca vocab=bce2969e
-/
@[simp] theorem mem_inertiaGroupOverDecompositionField_iff
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : L ≃ₐ[decompositionField K A] L) :
    σ ∈ inertiaGroupOverDecompositionField (K := K) A ↔
      ∃ τ : inertiaGroup K A,
        decompositionGroupEquivGalDecompositionField_of_finiteDimensional
          (K := K) A (τ : decompositionGroup K A) = σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩

/-- The transported inertia subgroup is normal in `Gal(L/Z_w)`.
@isnad1 id=normal.0h3v.s8.b612095cdc0c from=translated src=- shape=685ecb89 vocab=ed1c64b7
-/
instance inertiaGroupOverDecompositionField_normal
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (inertiaGroupOverDecompositionField (K := K) A).Normal := by
  let e :=
    decompositionGroupEquivGalDecompositionField_of_finiteDimensional
      (K := K) A
  simpa [inertiaGroupOverDecompositionField, e] using
    (Subgroup.Normal.map (inertiaGroup_normal (K := K) A)
      e.toMonoidHom e.surjective)

/-- The inertia-field definition source:
the fixed field of the transported inertia subgroup over `Z_w` is `T_w`.
@isnad1 id=eq.0h3v.s7.e617c7941fac from=translated src=- shape=f4e8a206 vocab=2f81cb33
-/
theorem inertiaFieldOverDecompositionField_fixedField_eq_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IntermediateField.fixedField
        (inertiaGroupOverDecompositionField (K := K) A) =
      inertiaFieldOverDecompositionField K A := by
  ext x
  rw [IntermediateField.mem_fixedField_iff,
    mem_inertiaFieldOverDecompositionField_iff]
  constructor
  · intro hx τ
    have hτ :
        decompositionGroupEquivGalDecompositionField_of_finiteDimensional
            (K := K) A (τ : decompositionGroup K A) ∈
          inertiaGroupOverDecompositionField (K := K) A := by
      exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩
    simpa using hx
      (decompositionGroupEquivGalDecompositionField_of_finiteDimensional
        (K := K) A (τ : decompositionGroup K A)) hτ
  · intro hx σ hσ
    rcases
      (mem_inertiaGroupOverDecompositionField_iff (K := K) A σ).mp hσ with
      ⟨τ, rfl⟩
    simpa using hx τ

/-- The inertia-field definition source:
`G(L/T_w)` over the decomposition field is the transported inertia subgroup.
@isnad1 id=eq.0h3v.s8.887901e61530 from=translated src=- shape=048caaf0 vocab=e446c2bb
-/
theorem inertiaFieldOverDecompositionField_fixingSubgroup_eq_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (inertiaFieldOverDecompositionField K A).fixingSubgroup =
      inertiaGroupOverDecompositionField (K := K) A := by
  rw [← inertiaFieldOverDecompositionField_fixedField_eq_of_finiteDimensional
    (K := K) A]
  exact
    IntermediateField.fixingSubgroup_fixedField
      (inertiaGroupOverDecompositionField (K := K) A)

/-- The inertia-field definition source:
the transported inertia group is the Galois group `G(L/T_w)` in the tower
`Z_w ⊆ T_w ⊆ L`.-/
def
inertiaGroupOverDecompositionFieldEquivGalInertiaFieldOverDecompositionField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    inertiaGroupOverDecompositionField (K := K) A ≃*
      (L ≃ₐ[inertiaFieldOverDecompositionField K A] L) :=
  (MulEquiv.subgroupCongr
      (inertiaFieldOverDecompositionField_fixingSubgroup_eq_of_finiteDimensional
        (K := K) A).symm).trans
    (IntermediateField.fixingSubgroupEquiv
      (inertiaFieldOverDecompositionField K A))

/-- The inertia-field definition:
the Galois correspondence gives
`G(L/Z_w)/I_w ≃ G(T_w/Z_w)`.-/
def decompositionQuotientInertiaEquivGalInertiaFieldOverDecomposition_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (L ≃ₐ[decompositionField K A] L) ⧸
        inertiaGroupOverDecompositionField (K := K) A ≃*
      (inertiaFieldOverDecompositionField K A ≃ₐ[decompositionField K A]
        inertiaFieldOverDecompositionField K A) := by
  rw [← inertiaFieldOverDecompositionField_fixedField_eq_of_finiteDimensional
    (K := K) A]
  exact
    IsGalois.normalAutEquivQuotient
      (inertiaGroupOverDecompositionField (K := K) A)

/-- The inertia-field definition source:
transport the quotient `G_w/I_w` along `G_w = G(L/Z_w)`.-/
def decompositionGroupQuotientInertiaEquivGalDecompositionQuotient_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (L ≃ₐ[decompositionField K A] L) ⧸
        inertiaGroupOverDecompositionField (K := K) A :=
  QuotientGroup.congr
    (inertiaGroup K A)
    (inertiaGroupOverDecompositionField (K := K) A)
    (decompositionGroupEquivGalDecompositionField_of_finiteDimensional
      (K := K) A)
    rfl

/-- The inertia-field definition:
`G_w/I_w ≃ G(T_w/Z_w)`, the group-theoretic part of the isomorphism
obtained from the residue-action exact sequence.-/
def decompositionGroupQuotientInertiaEquivGalInertiaFieldOverDecomposition_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (inertiaFieldOverDecompositionField K A ≃ₐ[decompositionField K A]
        inertiaFieldOverDecompositionField K A) :=
  (decompositionGroupQuotientInertiaEquivGalDecompositionQuotient_of_finiteDimensional
    (K := K) A).trans
    (decompositionQuotientInertiaEquivGalInertiaFieldOverDecomposition_of_finiteDimensional
      (K := K) A)

/-- The inertia-field definition source:
the inertia group is the Galois group over its fixed field.-/
def inertiaGroupInAutEquivGalInertiaField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    inertiaGroupInAut K A ≃* (L ≃ₐ[inertiaField K A] L) :=
  IntermediateField.subgroupEquivAlgEquiv (inertiaGroupInAut K A)

section IntermediateFieldFunctoriality

variable {M : Type*} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- Restrict scalars on automorphisms along an intermediate field
`K ⊆ M ⊆ L`.  This is the inclusion `G(L/M) -> G(L/K)` used in
scalar-restriction compatibility of ramification subgroups.-/
def restrictAutomorphismScalars : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L) where
  toFun σ :=
    { σ with
      commutes' := by
        intro a
        simp [IsScalarTower.algebraMap_eq K M L, σ.commutes (algebraMap K M a)] }
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

/-- scalar-restriction compatibility of ramification subgroups, decomposition-group membership form:
an `M`-automorphism stabilizes `A` exactly when the same automorphism, viewed
over `K`, stabilizes `A`.
@isnad1 id=iff.0h5v.s10.a721235b36cf from=translated src=- shape=1b5ad85f vocab=bc0f321e
-/
theorem mem_decompositionGroup_restrictScalars_iff
    (A : _root_.ValuationSubring L) (σ : L ≃ₐ[M] L) :
    restrictAutomorphismScalars (K := K) (M := M) σ ∈ decompositionGroup K A ↔
      σ ∈ decompositionGroup M A := by
  rfl

/-- Scalar restriction on decomposition groups along an intermediate field.-/
def decompositionGroupRestrictScalars
    (A : _root_.ValuationSubring L) :
    decompositionGroup M A →* decompositionGroup K A where
  toFun σ :=
    ⟨restrictAutomorphismScalars (K := K) (M := M) σ,
      (mem_decompositionGroup_restrictScalars_iff
        (K := K) (M := M) A σ).mpr σ.property⟩
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

/-- scalar-restriction compatibility of ramification subgroups, inertia-group membership form:
the residue action is unchanged by scalar restriction from `M` to `K`.
@isnad1 id=iff.0h5v.s13.f32f0d9a297b from=translated src=- shape=740c36da vocab=552ad2a7
-/
theorem mem_inertiaGroup_restrictScalars_iff
    (A : _root_.ValuationSubring L) (σ : decompositionGroup M A) :
    decompositionGroupRestrictScalars (K := K) (M := M) A σ ∈ inertiaGroup K A ↔
      σ ∈ inertiaGroup M A := by
  rfl

/-- Scalar restriction on inertia groups along an intermediate field.-/
def inertiaGroupRestrictScalars
    (A : _root_.ValuationSubring L) :
    inertiaGroup M A →* inertiaGroup K A where
  toFun σ :=
    ⟨decompositionGroupRestrictScalars (K := K) (M := M) A
        (σ : decompositionGroup M A),
      (mem_inertiaGroup_restrictScalars_iff
        (K := K) (M := M) A (σ : decompositionGroup M A)).mpr σ.property⟩
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

end IntermediateFieldFunctoriality

/-- The ordinary valuation-subring first-isomorphism form:
`D/I` is the range of the residue action.-/
def quotientInertiaEquivResidueActionRange
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (residueAction K A).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (residueAction_ker K A).symm).trans
    (QuotientGroup.quotientKerEquivRange (residueAction K A))

/-- States the theorem `quotientInertiaEquivResidueActionRange_mk`.
@isnad1 id=eq.0h4v.s17.98c4bdfcd805 from=translated src=- shape=1556b1ba vocab=e1929da2
-/
@[simp] theorem quotientInertiaEquivResidueActionRange_mk
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) :
    quotientInertiaEquivResidueActionRange (K := K) A
        (QuotientGroup.mk' (inertiaGroup K A) σ) =
      (residueAction K A).rangeRestrict σ :=
  rfl

/-- The inertia-field definition / the residue-action exact sequence source:
without surjectivity onto the whole residue automorphism group, the canonical
residue-field comparison is
`G(T_w/Z_w) ≃ range(G_w -> Aut(lambda))`.-/
def galInertiaFieldOverDecompositionEquivResidueActionRange_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (inertiaFieldOverDecompositionField K A ≃ₐ[decompositionField K A]
        inertiaFieldOverDecompositionField K A) ≃*
      (residueAction K A).range :=
  (decompositionGroupQuotientInertiaEquivGalInertiaFieldOverDecomposition_of_finiteDimensional
    (K := K) A).symm.trans
    (quotientInertiaEquivResidueActionRange (K := K) A)

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
