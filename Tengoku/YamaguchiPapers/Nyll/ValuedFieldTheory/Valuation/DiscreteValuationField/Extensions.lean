/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Tengoku.Seed.RingTheory.Valuation.Extension
import Tengoku.Seed.RingTheory.RamificationInertia.Basic
import Tengoku.Seed.NumberTheory.RamificationInertia.Inertia
import Tengoku.Seed.NumberTheory.RamificationInertia.Ramification
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.Algebra.Group.Units.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite extensions of discretely valued fields

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

namespace ValuationTheory

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The field degree of a finite valued extension.-/
def degree (_base : DVF.{u, v} K) (_target : DVF.{w, x} L) : ℕ :=
  Module.finrank K L

omit [FiniteDimensional K L]
    [base.valuation.HasExtension target.valuation] in
/-- The degree of a finite extension of discrete valuation fields is its linear `finrank`.
@isnad1 id=eq.0h4v.s6.974bf1814122 from=translated src=- shape=d2a81f83 vocab=2892ba06
-/
@[simp] theorem degree_eq_finrank :
    degree base target = Module.finrank K L :=
  rfl

/-- The canonical ramification index of the target maximal ideal over the
base maximal ideal.-/
noncomputable def ramificationIndex : ℕ :=
  Ideal.ramificationIdx'
    (base.maximalIdeal : Ideal base.valuationSubring)
    (target.maximalIdeal : Ideal target.valuationSubring)

/-- The canonical residue degree of the target maximal ideal over the base
maximal ideal.-/
noncomputable def residueDegree : ℕ :=
  (target.maximalIdeal : Ideal target.valuationSubring).inertiaDeg
    base.valuationSubring

/-- The induced map between valuation subrings.-/
def integerMap :
    base.valuationSubring →+* target.valuationSubring :=
  algebraMap base.valuationSubring target.valuationSubring

omit [FiniteDimensional K L] in
/-- The induced map between valuation subrings is injective.
@isnad1 id=injectiv.0h4v.s8.6d5485dd40c0 from=translated src=- shape=b769c090 vocab=798c1b2c
-/
theorem integerMap_injective :
    Function.Injective (integerMap base target) := by
  change Function.Injective
    (algebraMap base.valuation.valuationSubring
      target.valuation.valuationSubring)
  exact _root_.Valuation.HasExtension.algebraMap_injective
    (vK := base.valuation) (vA := target.valuation)

omit [FiniteDimensional K L] in
/-- The valuation-subring map evaluates through the ambient algebra map.
@isnad1 id=eq.0h5v.s8.cce875ca3de6 from=translated src=- shape=7935cef4 vocab=0c99ce43
-/
@[simp] theorem integerMap_apply (a : base.valuationSubring) :
    (((integerMap base target) a : target.valuationSubring) : L) =
      algebraMap K L (a : K) := by
  change ((algebraMap base.valuation.valuationSubring
    target.valuation.valuationSubring) a : L) = algebraMap K L (a : K)
  rfl

omit [FiniteDimensional K L] in
/-- Maximal-ideal membership is reflected by a valued extension.
@isnad1 id=iff.0h5v.s9.73f266cb3996 from=translated src=- shape=b55dd5de vocab=b160298f
-/
theorem integerMap_mem_maximalIdeal_iff (a : base.valuationSubring) :
    integerMap base target a ∈ target.maximalIdeal ↔
      a ∈ base.maximalIdeal := by
  rw [target.mem_maximalIdeal_iff (integerMap base target a),
    base.mem_maximalIdeal_iff a, integerMap_apply base target a]
  exact _root_.Valuation.HasExtension.val_map_lt_one_iff
    (vR := base.valuation) (vA := target.valuation) (a : K)

omit [FiniteDimensional K L] in
/-- The target maximal ideal pulls back to the base maximal ideal.
@isnad1 id=eq.0h4v.s8.4ad9077c0a02 from=translated src=- shape=a2bd4131 vocab=f233027f
-/
theorem maximalIdeal_comap_integerMap_eq :
    target.maximalIdeal.comap (integerMap base target) =
      base.maximalIdeal := by
  ext a
  exact integerMap_mem_maximalIdeal_iff base target a

omit [FiniteDimensional K L] in
/-- The image of the source maximal ideal in the target valuation ring is nonzero.
@isnad1 id=ne.0h4v.s9.dd82535b3051 from=translated src=- shape=3d261ca8 vocab=03023a54
-/
theorem maximalIdeal_map_integerMap_ne_bot :
    Ideal.map (integerMap base target) base.maximalIdeal ≠ ⊥ := by
  intro h
  exact base.maximalIdeal_ne_bot
    ((Ideal.map_eq_bot_iff_of_injective
      (integerMap_injective base target)).1 h)

omit [FiniteDimensional K L] in
/-- The source maximal ideal maps into the target maximal ideal.
@isnad1 id=le.0h4v.s9.1740d6b4822c from=translated src=- shape=60418346 vocab=40f27141
-/
theorem maximalIdeal_map_integerMap_le :
    Ideal.map (integerMap base target) base.maximalIdeal ≤
      target.maximalIdeal := by
  rw [Ideal.map_le_iff_le_comap,
    maximalIdeal_comap_integerMap_eq base target]

/- A valued extension preserves the residue-field characteristic. -/

/-- The induced map on residue fields.-/
def residueMap :
    base.residueField →+* target.residueField :=
  algebraMap base.residueField target.residueField

omit [FiniteDimensional K L] in
/-- The residue-field map sends the residue of an integer to its target residue.
@isnad1 id=eq.0h5v.s9.922e769f7a3d from=translated src=- shape=ba89b431 vocab=9d4e6aa3
-/
@[simp] theorem residueMap_residue (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  change
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
      (_root_.IsLocalRing.residue base.valuation.valuationSubring a) =
    _root_.IsLocalRing.residue target.valuation.valuationSubring
      ((algebraMap base.valuation.valuationSubring
        target.valuation.valuationSubring) a)
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field map of a valued extension is injective.
@isnad1 id=injectiv.0h4v.s7.a803350d91a7 from=translated src=- shape=b769c090 vocab=e97c3c71
-/
theorem residueMap_injective :
    Function.Injective (residueMap base target) := by
  change Function.Injective
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
  rw [ValuationTheory.DiscreteValuationField.ResidueField.algebraMap_eq_map_algebraMap]
  exact ValuationTheory.DiscreteValuationField.ResidueField.map_algebraMap_injective

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map upgrades its canonical injectivity to
bijectivity.
@isnad1 id=bijectiv.1h4v.s8.6c4044c20930 from=translated src=- shape=f10e1bd3 vocab=a4067e45
-/
theorem residueMap_bijective_of_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective (residueMap base target) :=
  ⟨residueMap_injective base target, hSurj⟩

omit [FiniteDimensional K L] in
/-- The residue-field isomorphism attached to a surjective residue map.-/
noncomputable def residueFieldEquivOfSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueField ≃+* target.residueField :=
  RingEquiv.ofBijective (residueMap base target)
    (residueMap_bijective_of_surjective base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-field equivalence induced by surjectivity evaluates by the residue map.
@isnad1 id=eq.1h5v.s9.3890927f783a from=translated src=- shape=c4f43b80 vocab=b1c93dc0
-/
@[simp] theorem residueFieldEquivOfSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    residueFieldEquivOfSurjective base target hSurj z =
      residueMap base target z :=
  rfl

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence recovers a source class after applying the residue map.
@isnad1 id=eq.1h5v.s9.7e0499940d17 from=translated src=- shape=7225a87a vocab=cb7ef6df
-/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_residueMap
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (residueMap base target z) = z := by
  simpa using
    (residueFieldEquivOfSurjective base target hSurj).symm_apply_apply z

omit [FiniteDimensional K L] in
/-- Applying the residue map after the inverse residue-field equivalence recovers
the target class.
@isnad1 id=eq.1h5v.s9.a615aba92196 from=translated src=- shape=1b6a8c79 vocab=cb7ef6df
-/
@[simp] theorem residueMap_residueFieldEquivOfSurjective_symm_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : target.residueField) :
    residueMap base target
        ((residueFieldEquivOfSurjective base target hSurj).symm z) = z :=
  (residueFieldEquivOfSurjective base target hSurj).apply_symm_apply z

/-- The induced map on unit groups of valuation rings.-/
def unitMap :
    base.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map (integerMap base target).toMonoidHom

omit [FiniteDimensional K L] in
/-- The induced unit map agrees with the valuation-ring map on underlying elements.
@isnad1 id=eq.0h5v.s10.de35a41f47fb from=translated src=- shape=9e85ddb8 vocab=be130395
-/
@[simp] theorem unitMap_apply (a : base.valuationSubringˣ) :
    ((unitMap base target a : target.valuationSubringˣ) :
        target.valuationSubring) =
      integerMap base target (a : base.valuationSubring) :=
  rfl

omit [FiniteDimensional K L] in
/-- The induced map on residue-field units is injective.
@isnad1 id=injectiv.0h4v.s9.876120bcd54b from=translated src=- shape=ea56c728 vocab=95efac4a
-/
theorem residueUnitsMap_injective :
    Function.Injective
      (Units.map (residueMap base target).toMonoidHom) :=
  Units.map_injective (residueMap_injective base target)

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map implies surjectivity on residue-field units.
@isnad1 id=surjecti.1h4v.s9.2fe9ad4e3590 from=translated src=- shape=a25a34e4 vocab=53850936
-/
theorem residueUnitsMap_surjective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Surjective
      (Units.map (residueMap base target).toMonoidHom) := by
  intro y
  obtain ⟨z, hz⟩ := hSurj (y : target.residueField)
  have hz0 : z ≠ 0 := by
    intro h
    exact y.ne_zero (by simpa [h] using hz.symm)
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  simpa using hz

omit [FiniteDimensional K L] in
/-- A surjective residue map induces a bijection on residue-field units.
@isnad1 id=bijectiv.1h4v.s9.30c34ad2240b from=translated src=- shape=dd59db95 vocab=2129a784
-/
theorem residueUnitsMap_bijective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective
      (Units.map (residueMap base target).toMonoidHom) :=
  ⟨residueUnitsMap_injective base target,
    residueUnitsMap_surjective_of_residueMap_surjective base target hSurj⟩

omit [FiniteDimensional K L] in
/-- The unit-group equivalence induced by a surjective residue map.-/
noncomputable def residueUnitsEquivOfResidueMapSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueFieldˣ ≃* target.residueFieldˣ :=
  MulEquiv.ofBijective (Units.map (residueMap base target).toMonoidHom)
    (residueUnitsMap_bijective_of_residueMap_surjective
      base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-unit equivalence evaluates by the induced residue-unit map.
@isnad1 id=eq.1h5v.s10.289af16c00d8 from=translated src=- shape=6d32e2b1 vocab=7cf7338e
-/
@[simp] theorem residueUnitsEquivOfResidueMapSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.residueFieldˣ) :
    residueUnitsEquivOfResidueMapSurjective base target hSurj a =
      Units.map (residueMap base target).toMonoidHom a :=
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field equivalence sends a source residue to the corresponding target residue.
@isnad1 id=eq.1h5v.s10.43162a196124 from=translated src=- shape=c107e7a1 vocab=69f30445
-/
@[simp] theorem residueFieldEquivOfSurjective_apply_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    residueFieldEquivOfSurjective base target hSurj (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  rw [residueFieldEquivOfSurjective_apply,
    residueMap_residue]

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence sends a target residue back to its source residue.
@isnad1 id=eq.1h5v.s10.4c12953bde27 from=translated src=- shape=d7cf04f7 vocab=6d2f3567
-/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_target_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (target.residueMap (integerMap base target a)) =
      base.residueMap a := by
  rw [← residueMap_residue base target,
    residueFieldEquivOfSurjective_symm_apply_residueMap]

/-- Unramified means that the canonical ramification index is one.-/
def IsUnramified : Prop :=
  ramificationIndex base target = 1

/-- Totally ramified means that the canonical residue degree is one.-/
def IsTotallyRamified : Prop :=
  residueDegree base target = 1

/-- Defectlessness is the exact fundamental equality.-/
def IsDefectless : Prop :=
  degree base target =
    ramificationIndex base target * residueDegree base target

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
