/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restricting a valuation to its multiplicative range

The restricted valuation has the same valuation ring, maximal ideal, and
residue field as the original valuation.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

section Field

variable [Field R]

/-- Restrict a valuation's codomain to its actual multiplicative range.

This removes irrelevant ambient value-group elements.  It is the value-group
normalization needed before finite-dimensional closedness can be used for an
abstract chosen local-field valuation.-/
def mrangeRestrict (v : _root_.Valuation R Gamma) :
    _root_.Valuation R (MonoidHom.mrange v.toMonoidWithZeroHom) where
  toFun r := ⟨v r, ⟨r, rfl⟩⟩
  map_one' := by
    ext
    exact map_one v
  map_zero' := by
    ext
    exact map_zero v
  map_mul' x y := by
    ext
    exact map_mul v x y
  map_add_le_max' x y := by
    rw [← Subtype.coe_le_coe]
    exact map_add_le_max v x y

/-- The defining evaluation formula for `mrangeRestrict` is `(mrangeRestrict v x : Gamma) = v x`.
@isnad1 id=eq.0h4v.s9.6d563f7ac3e5 from=translated src=- shape=a3b24924 vocab=f9a3abe1
-/
@[simp]
theorem mrangeRestrict_apply (v : _root_.Valuation R Gamma) (x : R) :
    (mrangeRestrict v x : Gamma) = v x :=
  rfl

/-- Passing to the actual multiplicative range does not change the valuation
subring predicate.
@isnad1 id=iff.0h4v.s7.03bd4974351a from=translated src=- shape=2d25dc12 vocab=510a33f1
-/
theorem mem_mrangeRestrict_valuationSubring_iff
    (v : _root_.Valuation R Gamma) (x : R) :
    x ∈ (mrangeRestrict v).valuationSubring ↔ x ∈ v.valuationSubring := by
  rw [_root_.Valuation.mem_valuationSubring_iff,
    _root_.Valuation.mem_valuationSubring_iff]
  rw [← Subtype.coe_le_coe]
  rfl

/-- The valuation subring is unchanged after restricting the value group to
the actual multiplicative range.-/
noncomputable def valuationSubringEquivMrangeRestrict
    (v : _root_.Valuation R Gamma) :
    v.valuationSubring ≃+* (mrangeRestrict v).valuationSubring where
  toFun x :=
    ⟨x, (mem_mrangeRestrict_valuationSubring_iff v x).2 x.2⟩
  invFun x :=
    ⟨x, (mem_mrangeRestrict_valuationSubring_iff v x).1 x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

/--
Establishes the identity `((valuationSubringEquivMrangeRestrict v x : (mrangeRestrict
v).valuationSubring) : R) = x`.
@isnad1 id=eq.0h4v.s12.554c9666c894 from=translated src=- shape=221a31c3 vocab=2c918daf
-/
@[simp]
theorem valuationSubringEquivMrangeRestrict_apply_coe
    (v : _root_.Valuation R Gamma) (x : v.valuationSubring) :
    ((valuationSubringEquivMrangeRestrict v x :
      (mrangeRestrict v).valuationSubring) : R) = x :=
  rfl

variable {K : Type u} [Field K]

/-- The valuation-subring equivalence induced by range restriction preserves
the maximal ideal.
@isnad1 id=iff.0h4v.s13.2a27339abc4b from=translated src=- shape=44ba580e vocab=586e2004
-/
theorem valuationSubringEquivMrangeRestrict_mem_maximalIdeal_iff
    (v : _root_.Valuation K Gamma) (x : v.valuationSubring) :
    valuationSubringEquivMrangeRestrict v x ∈
        IsLocalRing.maximalIdeal (mrangeRestrict v).valuationSubring ↔
      x ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
  rw [_root_.Valuation.mem_maximalIdeal_iff,
    _root_.Valuation.mem_maximalIdeal_iff]
  rw [← Subtype.coe_lt_coe]
  rfl

/--
Establishes the identity `(IsLocalRing.maximalIdeal v.valuationSubring).map
(valuationSubringEquivMrangeRestrict v : v.valuationSubring →+* (mrangeRestrict
v).valuationSubring) = IsLocalRing.maximalIdeal (mrangeRestrict v).valuationSubring`.
@isnad1 id=eq.0h3v.s13.eb3c9dee4f0a from=translated src=- shape=5cbd52ed vocab=3d793da0
-/
@[simp]
theorem valuationSubringEquivMrangeRestrict_map_maximalIdeal
    (v : _root_.Valuation K Gamma) :
    (IsLocalRing.maximalIdeal v.valuationSubring).map
        (valuationSubringEquivMrangeRestrict v :
          v.valuationSubring →+* (mrangeRestrict v).valuationSubring) =
      IsLocalRing.maximalIdeal (mrangeRestrict v).valuationSubring := by
  let e := valuationSubringEquivMrangeRestrict v
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring)
    e.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (valuationSubringEquivMrangeRestrict_mem_maximalIdeal_iff v x).2 hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp [e]⟩
    exact
      (valuationSubringEquivMrangeRestrict_mem_maximalIdeal_iff v (e.symm y)).1
        (by simpa [e] using hy)

/-- Restricting a valuation to its actual multiplicative range induces the
same residue field.-/
noncomputable def residueFieldEquivMrangeRestrict
    (v : _root_.Valuation K Gamma) :
    IsLocalRing.ResidueField v.valuationSubring ≃+*
      IsLocalRing.ResidueField (mrangeRestrict v).valuationSubring := by
  let e := valuationSubringEquivMrangeRestrict v
  letI : IsLocalHom
      (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring) :=
    IsLocalHom.of_surjective
      (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring)
      e.surjective
  exact IsLocalRing.ResidueField.mapEquiv e

end Field

end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
