/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.NormUnits
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

namespace LocalFieldTheory

noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The norm subgroup of `Kˣ` attached to `L/K`.-/
noncomputable def fieldNormSubgroup : Subgroup Kˣ :=
  (normUnits K L).range

/-- First-isomorphism-theorem form for the field norm on unit groups:
`Lˣ / ker(N)` is the norm subgroup of `Kˣ`.-/
noncomputable def fieldNormUnitsQuotientKerEquivFieldNormSubgroup :
    Lˣ ⧸ MonoidHom.ker (normUnits K L) ≃*
      fieldNormSubgroup K L :=
  QuotientGroup.quotientKerEquivRange (normUnits K L)

/--
Establishes the identity `fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) = (normUnits K L).rangeRestrict z`.
@isnad1 id=eq.0h3v.s12.58e3a2bc7bdb from=translated src=- shape=d63a3eec vocab=243475e3
-/
@[simp] theorem fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) =
      (normUnits K L).rangeRestrict z :=
  rfl

/--
Establishes the identity `((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) : fieldNormSubgroup K L) : Kˣ) = normUnits K L z`.
@isnad1 id=eq.0h3v.s12.9312d8a7a5fa from=translated src=- shape=dfa8d7e7 vocab=55c571a3
-/
@[simp] theorem coe_fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    ((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) :
        fieldNormSubgroup K L) : Kˣ) =
      normUnits K L z :=
  rfl

/-- The quotient map `Kˣ → Kˣ / N_{L/K}(Lˣ)` attached to the field norm.-/
noncomputable def fieldNormQuotientMap :
    Kˣ →* Kˣ ⧸ fieldNormSubgroup K L :=
  QuotientGroup.mk' (fieldNormSubgroup K L)

/--
The defining evaluation formula for `fieldNormQuotientMap` is `fieldNormQuotientMap K L x =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
@isnad1 id=eq.0h3v.s10.994c9f223279 from=translated src=- shape=525ff086 vocab=2bfc550f
-/
@[simp] theorem fieldNormQuotientMap_apply (x : Kˣ) :
    fieldNormQuotientMap K L x =
      QuotientGroup.mk' (fieldNormSubgroup K L) x :=
  rfl

/-- Norm of an element coming from the base field.
@isnad1 id=eq.0h3v.s9.fc5ecffb2a5c from=translated src=- shape=1df33993 vocab=b6093619
-/
@[simp] theorem fieldNormUnits_algebraMap (u : Kˣ) :
    normUnits K L (Units.map (algebraMap K L).toMonoidHom u) =
      u ^ Module.finrank K L := by
  ext
  simp [normUnits, Algebra.norm_algebraMap]

/-- Package a field norm as a `ValuedNorm` once the valuation formula has been
proved for the concrete extension.  The natural-number argument is not a
second source of extension-invariant data: `hformula` certifies it as the
valuation multiplier (and a source uniformizer makes that multiplier unique).-/
@[reducible] noncomputable def valuedFieldNorm
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    ValuedNorm vK vL where
  toHom := normUnits K L
  residueDegree := residueDegree
  valuation_formula := hformula

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).toHom =
normUnits K L`.
@isnad1 id=eq.1h5v.s9.4e40a4e6a0b0 from=translated src=- shape=1c118593 vocab=ae0e53af
-/
@[simp] theorem valuedFieldNorm_toHom
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).toHom =
      normUnits K L :=
  rfl

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
fieldNormSubgroup K L`.
@isnad1 id=eq.1h5v.s8.6d360389d136 from=translated src=- shape=a643be2f vocab=f6e2e680
-/
theorem valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
      fieldNormSubgroup K L := by
  ext x
  rfl

/-- Concrete cyclic description of the field-norm quotient.  The assumptions
are the valuation formula for the field norm and the assertion that every
target valuation-zero element is already a field norm.-/
noncomputable def fieldNormQuotientEquivZMod
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    Kˣ ⧸ fieldNormSubgroup K L ≃* Multiplicative (ZMod residueDegree) :=
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  (QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
    (N.normQuotientEquivZMod hϖK hϖL hzero')

/--
Establishes the identity `fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL
hzero (QuotientGroup.mk' (fieldNormSubgroup K L) x) = Multiplicative.ofAdd ((vK.val x : ℤ) : ZMod
residueDegree)`.
@isnad1 id=eq.4h8v.s11.9c6330daea19 from=translated src=- shape=b91d7683 vocab=5241ec6a
-/
@[simp] theorem fieldNormQuotientEquivZMod_mk
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x : Kˣ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        (QuotientGroup.mk' (fieldNormSubgroup K L) x) =
      Multiplicative.ofAdd ((vK.val x : ℤ) : ZMod residueDegree) := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  unfold fieldNormQuotientEquivZMod
  rw [MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  simpa [N, valuedFieldNorm] using
    N.normQuotientEquivZMod_mk hϖK hϖL hzero' x

/--
`fieldNormQuotientEquivZMod_uniformizer` satisfies the integer-power formula
`fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL hzero (QuotientGroup.mk'
(fieldNormSubgroup K L) (ϖK ^ n)) = Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)`.
@isnad1 id=eq.4h8v.s11.105c7b03af93 from=translated src=- shape=226632db vocab=bd60f55f
-/
@[simp] theorem fieldNormQuotientEquivZMod_uniformizer_zpow
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        (QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n)) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree) := by
  rw [fieldNormQuotientEquivZMod_mk K L vK vL residueDegree
      hformula hϖK hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
`fieldNormQuotientEquivZMod_uniformizerClass` satisfies the integer-power formula
`fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL hzero ((QuotientGroup.mk'
(fieldNormSubgroup K L) ϖK) ^ n) = Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)`.
@isnad1 id=eq.4h8v.s11.da2f2083d56f from=translated src=- shape=2c6bb9de vocab=bd60f55f
-/
@[simp] theorem fieldNormQuotientEquivZMod_uniformizerClass_zpow
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        ((QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree) := by
  have hpow : QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) ϖK n
  rw [← hpow,
    fieldNormQuotientEquivZMod_uniformizer_zpow K L vK vL
      residueDegree hformula hϖK hϖL hzero n]

/--
Establishes the identity `(fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL
hzero).symm (Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)) = QuotientGroup.mk'
(fieldNormSubgroup K L) (ϖK ^ n)`.
@isnad1 id=eq.4h8v.s11.a21473ede69d from=translated src=- shape=635a2dd2 vocab=12df9645
-/
@[simp] theorem fieldNormQuotientEquivZMod_symm_mk_ofAdd
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    (fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero).symm
        (Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)) =
      QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) := by
  apply (fieldNormQuotientEquivZMod K L vK vL residueDegree
    hformula hϖK hϖL hzero).injective
  rw [MulEquiv.apply_symm_apply,
    fieldNormQuotientEquivZMod_uniformizer_zpow K L vK vL
      residueDegree hformula hϖK hϖL hzero n]

/-- Concrete compatibility condition saying that the field norm maps the
`n`-th source principal-unit subgroup into the requested target level.-/
abbrev fieldNormMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) : Prop :=
  ∀ n {x : Lˣ}, x ∈ UL.principalUnitSubgroup n →
    normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)

/-- The field norm restricted to a principal-unit filtration level.-/
def fieldNormMapLevelOfMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ) :
    UL.principalUnitSubgroup n →*
      UK.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨normUnits K L x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact (normUnits K L).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (normUnits K L).map_mul x.1 y.1

/--
The defining evaluation formula for `fieldNormMapLevelOfMapsFiltrationLevels` is
`(fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x : Kˣ) = normUnits K L
x.1`.
@isnad1 id=eq.1h7v.s12.8dc5daa4b6ba from=translated src=- shape=8af52b43 vocab=8725d2b8
-/
@[simp] theorem fieldNormMapLevelOfMapsFiltrationLevels_apply
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    (x : UL.principalUnitSubgroup n) :
    (fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x :
        Kˣ) =
      normUnits K L x.1 :=
  rfl

/-- The field norm descended to quotients by compatible principal-unit
filtration levels.-/
def fieldNormFiltrationQuotientMap
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    Lˣ ⧸ UL.principalUnitSubgroup n →*
      Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L) (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `fieldNormFiltrationQuotientMap` is
`fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk x) = QuotientGroup.mk
(normUnits K L x)`.
@isnad1 id=eq.1h7v.s11.c60521fb23bf from=translated src=- shape=7d34dd82 vocab=f8486a43
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (normUnits K L x) :=
  rfl

/--
Establishes the identity `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
(QuotientGroup.mk' (UL.principalUnitSubgroup n) x) = QuotientGroup.mk' (UK.principalUnitSubgroup
(targetLevel n)) (normUnits K L x)`.
@isnad1 id=eq.1h7v.s12.75d2ebe3e78a from=translated src=- shape=6bf00431 vocab=cea86b1f
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk'
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UK.principalUnitSubgroup (targetLevel n))
        (normUnits K L x) :=
  rfl

/-- The preimage of a target principal-unit filtration subgroup under the
field norm.-/
def fieldNormFiltrationPreimageSubgroup
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ) :
    Subgroup Lˣ :=
  (UK.principalUnitSubgroup (targetLevel n)).comap (normUnits K L)

/--
Characterizes `x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n` by the equivalent
condition `normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)`.
@isnad1 id=iff.0h6v.s8.98d84eab52f0 from=translated src=- shape=dd00bf39 vocab=af7185a0
-/
@[simp] theorem mem_fieldNormFiltrationPreimageSubgroup_iff
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    (x : Lˣ) :
    x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n ↔
      normUnits K L x ∈
        UK.principalUnitSubgroup (targetLevel n) :=
  Iff.rfl

/--
The subgroup appearing in `(fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal` is
normal.
@isnad1 id=normal.0h5v.s7.9c4243a069a8 from=translated src=- shape=27de092c vocab=3b102094
-/
instance fieldNormFiltrationPreimageSubgroup_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageSubgroup]
  infer_instance

/-- The class of the field-norm preimage of the target filtration subgroup
inside the source filtration quotient.-/
def fieldNormFiltrationPreimageClassInQuotient
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal] :
    Subgroup (Lˣ ⧸ UL.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UL.principalUnitSubgroup n))
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n)

/--
The subgroup appearing in `(fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel
n).Normal` is normal.
@isnad1 id=normal.0h6v.s8.d3f340182c7a from=translated src=- shape=7dd3a6a0 vocab=a33c643a
-/
instance fieldNormFiltrationPreimageClassInQuotient_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageClassInQuotient
      K L UK UL targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageClassInQuotient]
  infer_instance

/-- The kernel of the concrete field-norm filtration quotient map is the class
of the norm-preimage of the target filtration subgroup.
@isnad1 id=eq.1h6v.s9.57c4a3d241f9 from=translated src=- shape=9d5cc32d vocab=ad3ac445
-/
theorem fieldNormFiltrationQuotientMap_ker_eq_preimageClass
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).ker =
      fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n := by
  exact QuotientGroup.ker_map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L)
    (by intro x hx; exact hN n hx)

/-- First-isomorphism form of the concrete field-norm filtration quotient map,
with codomain the actual range when no surjectivity hypothesis is available.-/
noncomputable def fieldNormFiltrationQuotientModuloPreimageClassEquivRange
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (Lˣ ⧸ UL.principalUnitSubgroup n) ⧸
        fieldNormFiltrationPreimageClassInQuotient
          K L UK UL targetLevel n ≃*
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (fieldNormFiltrationQuotientMap_ker_eq_preimageClass
        K L UK UL targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n))

/--
Establishes the identity `fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) = (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).rangeRestrict q`.
@isnad1 id=eq.1h7v.s15.e8a39a0c0618 from=translated src=- shape=6f3fe166 vocab=807561e6
-/
@[simp] theorem fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) =
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `((fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) : (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).range) : Kˣ ⧸
UK.principalUnitSubgroup (targetLevel n)) = fieldNormFiltrationQuotientMap K L UK UL targetLevel
hN n q`.
@isnad1 id=eq.1h7v.s14.72fe519ffc9b from=translated src=- shape=d0170a0a vocab=655f5b29
-/
@[simp] theorem coe_fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    ((fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) :
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).range) :
        Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n)) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q := by
  rw [fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk]
  rfl

/-- First-isomorphism form of a surjective concrete field-norm filtration
quotient map.-/
noncomputable def fieldNormFiltrationQuotientModuloPreimageClassEquivTarget
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n)) :
    (Lˣ ⧸ UL.principalUnitSubgroup n) ⧸
        fieldNormFiltrationPreimageClassInQuotient
          K L UK UL targetLevel n ≃*
      Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n) :=
  (QuotientGroup.quotientMulEquivOfEq
      (fieldNormFiltrationQuotientMap_ker_eq_preimageClass
        K L UK UL targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n) hSurj)

/--
Establishes the identity `fieldNormFiltrationQuotientModuloPreimageClassEquivTarget K L UK UL
targetLevel hN n hSurj (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) = fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q`.
@isnad1 id=eq.2h7v.s14.23d5fb5776cc from=translated src=- shape=7c7c47be vocab=df50bd65
-/
@[simp] theorem fieldNormFiltrationQuotientModuloPreimageClassEquivTarget_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n))
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientModuloPreimageClassEquivTarget
        K L UK UL targetLevel hN n hSurj
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q := by
  rw [fieldNormFiltrationQuotientModuloPreimageClassEquivTarget,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse]
  exact QuotientGroup.kerLift_mk
    (φ := fieldNormFiltrationQuotientMap
      K L UK UL targetLevel hN n) q

end DiscreteValuationField

end

end LocalFieldTheory
