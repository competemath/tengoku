/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete discretely valued fields
-/

namespace ValuationTheory

noncomputable section

universe u v w

namespace DiscreteValuationField

namespace Valuation

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- A complete discrete valuation.-/
class IsCompleteDiscrete (val : _root_.Valuation K Gamma) : Prop where
  /-- A complete discrete valuation has discrete rank one.-/
  [isRankOneDiscrete : val.IsRankOneDiscrete]
  /-- The valuation ring is complete for its maximal-ideal adic topology.-/
  isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring

attribute [instance] IsCompleteDiscrete.isRankOneDiscrete

/-- Completeness of the valued field implies adic completeness of its valuation subring.
@isnad1 id=isadicco.0h3v.s8.5f7c10ddaca9 from=translated src=- shape=733f2c77 vocab=0a0c1866
-/
theorem isAdicComplete (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring :=
  IsCompleteDiscrete.isAdicComplete (val := val)

/-- The valuation subring of a complete discrete valuation field is henselian.
@isnad1 id=henselia.0h3v.s6.3d2648376bc8 from=translated src=- shape=dc6ca1dc vocab=d1e12235
-/
theorem henselianRing (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    HenselianRing val.valuationSubring (IsLocalRing.maximalIdeal val.valuationSubring) := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring)
      val.valuationSubring := isAdicComplete val
  infer_instance

/-- In a rank-one discrete valuation ring, membership in the `n`-th power of
the maximal ideal is the same as the corresponding valuation bound against a
chosen uniformizer power.
@isnad1 id=iff.1h6v.s10.024249f31c40 from=translated src=- shape=a8d7b7ba vocab=3140e14a
-/
theorem mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
    (val : _root_.Valuation K Gamma) [val.IsRankOneDiscrete]
    {pi x : val.valuationSubring}
    (hpi : val.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔
      val (x : K) ≤ val ((pi ^ n : val.valuationSubring) : K) := by
  rw [hpi.is_generator, Ideal.span_singleton_pow]
  simpa [Ideal.mem_span_singleton] using
    (_root_.Valuation.Integers.dvd_iff_le
      (_root_.Valuation.valuationSubring.integers (v := val))
      (x := pi ^ n) (y := x))

end Valuation

/-- A field with a chosen complete rank-one discrete valuation.-/
structure CompleteDVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group.-/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group.-/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field.-/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation is complete and discretely rank one.-/
  [instCompleteDiscrete : Valuation.IsCompleteDiscrete valuation]

attribute [instance] CompleteDVF.instValueGroup CompleteDVF.instCompleteDiscrete

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- A complete DVF is Henselian.  This is the canonical forgetful projection:
all weaker DVF data are obtained through this object.-/
abbrev toHenselianDVF (F : CompleteDVF.{u, v} K) : HenselianDVF.{u, v} K where
  toDVF :=
    { ValueGroup := F.ValueGroup
      valuation := F.valuation }
  instHenselian := by
    change HenselianRing F.valuation.valuationSubring
      (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    exact Valuation.henselianRing F.valuation

/-- The underlying DVF, obtained along the canonical
`CompleteDVF -> HenselianDVF -> DVF` path.-/
abbrev toDVF (F : CompleteDVF.{u, v} K) : DVF.{u, v} K :=
  F.toHenselianDVF.toDVF

/-- Introduces the abbreviation `valuationSubring`.-/
abbrev valuationSubring (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.valuationSubring

/-- Introduces the abbreviation `maximalIdeal`.-/
abbrev maximalIdeal (F : CompleteDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toHenselianDVF.maximalIdeal

/-- Introduces the abbreviation `residueField`.-/
abbrev residueField (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.residueField

/-- Introduces the abbreviation `residueMap`.-/
abbrev residueMap (F : CompleteDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toHenselianDVF.residueMap

/-- The valuation subring in the complete model is a discrete valuation ring.
@isnad1 id=isdiscre.0h2v.s5.b42c8a2c5014 from=translated src=- shape=1fcfa16f vocab=00a1e05f
-/
theorem valuationSubring_isDiscreteValuationRing (F : CompleteDVF.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring :=
  F.toDVF.valuationSubring_isDiscreteValuationRing

/-- The complete DVR model is complete for its maximal-ideal-adic topology.
@isnad1 id=isadicco.0h2v.s7.ffc1b3f0a239 from=translated src=- shape=f70856c2 vocab=c6418486
-/
theorem isAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring := by
  change IsAdicComplete
    (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    F.valuation.valuationSubring
  exact Valuation.isAdicComplete F.valuation

/-- The complete DVR valuation ring carries its canonical adic-completeness instance.
@isnad1 id=isadicco.0h2v.s7.ffc1b3f0a239 from=translated src=- shape=f70856c2 vocab=c6418486
-/
instance instIsAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring :=
  F.isAdicComplete

/-- Membership in the valuation subring is characterized by nonnegative valuation.
@isnad1 id=iff.0h3v.s7.657aa293ae46 from=translated src=- shape=c360bd7c vocab=fc8ba33e
-/
theorem mem_valuationSubring_iff (F : CompleteDVF.{u, v} K) (x : K) :
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1 :=
  F.toDVF.mem_valuationSubring_iff x

/-- Membership in the maximal ideal is characterized by strictly positive valuation.
@isnad1 id=iff.0h3v.s9.b87225fa6078 from=translated src=- shape=bc7453ea vocab=b2757e42
-/
theorem mem_maximalIdeal_iff (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    x ∈ F.maximalIdeal ↔ F.valuation (x : K) < 1 :=
  F.toDVF.mem_maximalIdeal_iff x

/-- An integral element has zero residue exactly when it lies in the maximal ideal.
@isnad1 id=iff.0h3v.s9.2bb942c59183 from=translated src=- shape=70818a76 vocab=06008366
-/
theorem residue_eq_zero_iff (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x = 0 ↔ x ∈ F.maximalIdeal :=
  IsLocalRing.residue_eq_zero_iff x

/-- An integral element has nonzero residue exactly when it is a unit.
@isnad1 id=iff.0h3v.s8.da5ae5b5301f from=translated src=- shape=6f15ab5f vocab=e42aa3ae
-/
theorem residue_ne_zero_iff_isUnit (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x ≠ 0 ↔ IsUnit x :=
  IsLocalRing.residue_ne_zero_iff_isUnit x

/-- Every residue-field element has a representative in the valuation ring.
@isnad1 id=surjecti.0h2v.s7.e8a21ae0e095 from=translated src=- shape=82667425 vocab=d3e2e3e9
-/
theorem residue_surjective (F : CompleteDVF.{u, v} K) :
    Function.Surjective F.residueMap :=
  IsLocalRing.residue_surjective

/-- A complete discrete valuation field admits a uniformizer.
@isnad1 id=ex.0h2v.s6.74a9454ba152 from=translated src=- shape=26bca203 vocab=a4216a47
-/
theorem exists_uniformizer (F : CompleteDVF.{u, v} K) :
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K)) :=
  F.toDVF.exists_uniformizer

/-- Every chosen uniformizer lies in the maximal ideal.
@isnad1 id=mem.1h3v.s8.61fb2839f173 from=translated src=- shape=687db7ab vocab=e1f8158e
-/
theorem uniformizer_mem_maximalIdeal (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∈ F.maximalIdeal :=
  F.toDVF.uniformizer_mem_maximalIdeal hpi

/-- The maximal ideal is the principal ideal generated by a uniformizer.
@isnad1 id=eq.1h3v.s7.9ae47b8b3427 from=translated src=- shape=fc41eb51 vocab=d0b153f7
-/
theorem maximalIdeal_eq_span_uniformizer (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    F.maximalIdeal = Ideal.span ({pi} : Set F.valuationSubring) :=
  F.toDVF.maximalIdeal_eq_span_uniformizer hpi

/-- Powers of the maximal ideal are generated by powers of any chosen
uniformizer.
@isnad1 id=eq.1h4v.s9.82a9f5322392 from=translated src=- shape=a2083ed1 vocab=71256b8c
-/
theorem maximalIdeal_pow_eq_span_uniformizer_pow (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    F.maximalIdeal ^ n = Ideal.span ({pi ^ n} : Set F.valuationSubring) :=
  F.toDVF.maximalIdeal_pow_eq_span_uniformizer_pow hpi n

/-- Membership in a power of the maximal ideal is divisibility by the
corresponding power of a uniformizer.
@isnad1 id=iff.1h5v.s9.2b8fdb5e81a6 from=translated src=- shape=53727752 vocab=825218bb
-/
theorem mem_maximalIdeal_pow_iff_uniformizer_pow_dvd (F : CompleteDVF.{u, v} K)
    {pi x : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ F.maximalIdeal ^ n ↔ pi ^ n ∣ x :=
  F.toDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hpi n

/-- Every nonzero ideal in the valuation ring of a complete DVF is a power of
the maximal ideal.
@isnad1 id=ex.1h3v.s9.01802657d1e6 from=translated src=- shape=d8d13e7c vocab=7d7fd193
-/
theorem nonzero_ideal_eq_maximalIdeal_pow (F : CompleteDVF.{u, v} K)
    (I : Ideal F.valuationSubring) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = F.maximalIdeal ^ n :=
  F.toDVF.nonzero_ideal_eq_maximalIdeal_pow I hI

/-- The maximal ideal of a complete DVF valuation ring is nonzero.
@isnad1 id=ne.0h2v.s8.91d9b1dd6923 from=translated src=- shape=6f5c5ab9 vocab=f924df04
-/
theorem maximalIdeal_ne_bot (F : CompleteDVF.{u, v} K) :
    F.maximalIdeal ≠ ⊥ := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  intro hbot
  have hmem : pi ∈ (⊥ : Ideal F.valuationSubring) := by
    rw [← hbot]
    exact F.uniformizer_mem_maximalIdeal hpi
  have hzero_sub : pi = 0 := by
    simpa using hmem
  apply hpi.ne_zero
  exact Subtype.ext_iff.mp hzero_sub

/-- No power of a uniformizer lies one step deeper in the maximal-ideal
filtration.
@isnad1 id=not.1h4v.s9.de02659bded6 from=translated src=- shape=2a9b1ee7 vocab=4c4e9c63
-/
theorem uniformizer_pow_not_mem_maximalIdeal_pow_succ
    (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    pi ^ n ∉ F.maximalIdeal ^ (n + 1) :=
  F.toDVF.uniformizer_pow_not_mem_maximalIdeal_pow_succ hpi n

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
