/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Ideal.Quotient.Index
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Develops quotients of valuation-ring units by higher principal units and compares their first
layer with residue-field units.
-/

namespace LocalFieldTheory

open ValuationTheory

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField.DVF

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- A valuation-ring-preserving field automorphism induces a ring automorphism
on every quotient `O/m^n`.-/
noncomputable def quotientMaximalIdealPowRingEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    F.valuationSubring ⧸ F.maximalIdeal ^ n ≃+*
      F.valuationSubring ⧸ F.maximalIdeal ^ n := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hpow :
      F.maximalIdeal ^ n =
        (F.maximalIdeal ^ n).map
          (r : F.valuationSubring →+* F.valuationSubring) := by
    rw [Ideal.map_pow, hmax]
  exact
    Ideal.quotientEquiv (F.maximalIdeal ^ n) (F.maximalIdeal ^ n) r
      hpow

/--
Establishes the identity `quotientMaximalIdealPowRingEquivOfPreserves F e hmem n
(Ideal.Quotient.mk (F.maximalIdeal ^ n) x) = Ideal.Quotient.mk (F.maximalIdeal ^ n)
(valuationSubringRingEquivOfPreserves F e hmem x)`.
@isnad1 id=eq.1h5v.s14.5e1ac1fdfa0a from=translated src=- shape=d0079bc9 vocab=139c3259
-/
@[simp] theorem quotientMaximalIdealPowRingEquivOfPreserves_mk
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (x : F.valuationSubring) :
    quotientMaximalIdealPowRingEquivOfPreserves F e hmem n
        (Ideal.Quotient.mk (F.maximalIdeal ^ n) x) =
      Ideal.Quotient.mk (F.maximalIdeal ^ n)
        (valuationSubringRingEquivOfPreserves F e hmem x) := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hpow :
      F.maximalIdeal ^ n =
        (F.maximalIdeal ^ n).map
          (r : F.valuationSubring →+* F.valuationSubring) := by
    rw [Ideal.map_pow, hmax]
  exact
    Ideal.quotientEquiv_mk (F.maximalIdeal ^ n) (F.maximalIdeal ^ n) r
      hpow x

/-- Reduction of valuation-ring units modulo the `n`-th power of the maximal
ideal.-/
def quotientUnitHom (n : ℕ) :
    F.valuationSubringˣ →*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ :=
  Units.map (Ideal.Quotient.mk (F.maximalIdeal ^ n))

/--
The defining evaluation formula for `quotientUnitHom` is
`((higherPrincipalUnitGroup.quotientUnitHom F n u : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
F.valuationSubring ⧸ F.maximalIdeal ^ n) = Ideal.Quotient.mk (F.maximalIdeal ^ n) (u :
F.valuationSubring)`.
@isnad1 id=eq.0h4v.s13.6f26cd3fb9e1 from=translated src=- shape=170ff198 vocab=fa8ed209
-/
@[simp] theorem quotientUnitHom_apply (n : ℕ) (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.quotientUnitHom F n u :
        (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
      F.valuationSubring ⧸ F.maximalIdeal ^ n) =
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) :=
  rfl

/-- The kernel of unit reduction modulo `m^n` is exactly the concrete
principal-unit subgroup `U^n`.
@isnad1 id=eq.0h3v.s11.3a68783a2538 from=translated src=- shape=172d0ed2 vocab=ab63a3af
-/
theorem quotientUnitHom_ker_eq (n : ℕ) :
    (higherPrincipalUnitGroup.quotientUnitHom F n).ker =
      higherPrincipalUnitGroup F n := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.mem_iff]
  constructor
  · intro hu
    have hval := congrArg
      (fun z : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ =>
        (z : F.valuationSubring ⧸ F.maximalIdeal ^ n)) hu
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1 at hval
    have hmk :
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ n)
            (1 : F.valuationSubring) := by
      simpa using hval
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).1 hmk
  · intro hu
    apply Units.ext
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1
    simpa using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).2 hu

/-- First-isomorphism form of unit reduction modulo `m^n`: `O^*/U^n` is the
range of the unit group of `O/m^n`.-/
noncomputable def unitsModHigherPrincipalUnitGroupEquivRange (n : ℕ) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      (higherPrincipalUnitGroup.quotientUnitHom F n).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (higherPrincipalUnitGroup.quotientUnitHom_ker_eq F n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (higherPrincipalUnitGroup.quotientUnitHom F n))

/-- For `n ≥ 1`, every unit modulo `m^n` is the reduction of a valuation-ring
unit.
@isnad1 id=surjecti.1h3v.s13.fdb12e93fa60 from=translated src=- shape=50eeddac vocab=93868b22
-/
theorem quotientUnitHom_surjective_of_pos {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (higherPrincipalUnitGroup.quotientUnitHom F n) := by
  intro y
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective
      (((y : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
        F.valuationSubring ⧸ F.maximalIdeal ^ n))
  have ha_unit : IsUnit a := by
    by_contra hnot
    have ha_mem : a ∈ F.maximalIdeal := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact (mem_nonunits_iff).2 hnot
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective
        (((y⁻¹ : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
          F.valuationSubring ⧸ F.maximalIdeal ^ n))
    have habq :
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (a * b) =
          (1 : F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
      calc
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (a * b) =
            Ideal.Quotient.mk (F.maximalIdeal ^ n) a *
              Ideal.Quotient.mk (F.maximalIdeal ^ n) b :=
          map_mul (Ideal.Quotient.mk (F.maximalIdeal ^ n)) a b
        _ = ((y : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
              F.valuationSubring ⧸ F.maximalIdeal ^ n) *
              ((y⁻¹ : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
                F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
              rw [ha, hb]
        _ = 1 := Units.mul_inv y
    have hdiff_pow : a * b - 1 ∈ F.maximalIdeal ^ n := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (a * b) (1 : F.valuationSubring)).1
        (by simpa using habq)
    have hn0 : n ≠ 0 := by omega
    have hdiff_max : a * b - 1 ∈ F.maximalIdeal :=
      Ideal.pow_le_self hn0 hdiff_pow
    have hab_mem : a * b ∈ F.maximalIdeal :=
      F.maximalIdeal.mul_mem_right b ha_mem
    have hone : (1 : F.valuationSubring) ∈ F.maximalIdeal := by
      have hsub : a * b - (a * b - 1) ∈ F.maximalIdeal :=
        F.maximalIdeal.sub_mem hab_mem hdiff_max
      rwa [sub_sub_cancel] at hsub
    exact (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime.one_notMem hone
  rcases ha_unit with ⟨u, rfl⟩
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa [higherPrincipalUnitGroup.quotientUnitHom_apply] using ha

/-- The unit-quotient coordinate theorem, first unit-quotient form:
`O^*/U^n ≃ (O/m^n)^*` for `n ≥ 1`.-/
noncomputable def unitsModHigherPrincipalUnitGroupEquivQuotientUnits
    (n : ℕ) (hn : 1 ≤ n) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
    (higherPrincipalUnitGroup.quotientUnitHom_ker_eq F n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (higherPrincipalUnitGroup.quotientUnitHom F n)
      (higherPrincipalUnitGroup.quotientUnitHom_surjective_of_pos F hn))

/-- The concrete principal-unit filtration as the abstract filtration API.-/
def toPrincipalUnitFiltration :
    AntitoneSubgroupFiltration F.valuationSubringˣ where
  subgroup := higherPrincipalUnitGroup F
  antitone := fun h => higherPrincipalUnitGroup.antitone F h

/--
Establishes the identity `(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).subgroup n =
higherPrincipalUnitGroup F n`.
@isnad1 id=eq.0h3v.s8.0da620857bc9 from=translated src=- shape=9a7ec49e vocab=c01801cd
-/
@[simp] theorem toPrincipalUnitFiltration_subgroup (n : ℕ) :
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).subgroup n =
      higherPrincipalUnitGroup F n :=
  rfl

/-! ### Successive principal-unit quotients -/

/-- The adjacent quotient `U^n/U^(n+1)` for the concrete complete-DVF
principal-unit filtration.-/
def principalUnitSuccQuot (n : ℕ) : Type u :=
  higherPrincipalUnitGroup F n ⧸
    (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)

/--
Equips the target with its canonical `CommGroup` structure, namely `CommGroup
(higherPrincipalUnitGroup.principalUnitSuccQuot F n)`.-/
instance principalUnitSuccQuotCommGroup (n : ℕ) :
    CommGroup (higherPrincipalUnitGroup.principalUnitSuccQuot F n) := by
  change CommGroup
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  infer_instance

/-- Explicit access to the concrete quotient used to implement
`principalUnitSuccQuot`.-/
def principalUnitSuccQuotConcreteEquiv (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) ≃*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact MulEquiv.refl _

/-- The quotient map `U^n → U^n/U^(n+1)`.-/
def principalUnitSuccQuotMk (n : ℕ) :
    higherPrincipalUnitGroup F n →*
      higherPrincipalUnitGroup.principalUnitSuccQuot F n := by
  change higherPrincipalUnitGroup F n →*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact QuotientGroup.mk' ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = QuotientGroup.mk u`.
@isnad1 id=eq.0h4v.s15.160c04f60ac1 from=translated src=- shape=e63afb45 vocab=a094bec5
-/
@[simp] theorem principalUnitSuccQuotConcreteEquiv_mk (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
      QuotientGroup.mk u :=
  rfl

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n)`.
@isnad1 id=surjecti.0h3v.s13.78e91447936e from=translated src=- shape=d45df13f vocab=08bba0ed
-/
theorem principalUnitSuccQuotMk_surjective (n : ℕ) :
    Function.Surjective (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n) :=
  QuotientGroup.mk'_surjective ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

/-- Descend a homomorphism from `U^n` that kills `U^(n+1)`.-/
def principalUnitSuccQuotLift
    {H : Type*} [Group H] (n : ℕ)
    (f : higherPrincipalUnitGroup F n →* H)
    (h : (higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n) ≤ f.ker) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n →* H := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) →* H
  exact QuotientGroup.lift
    ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n)) f h

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotLift F n f h
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = f u`.
@isnad1 id=eq.1h6v.s14.ddcc4a0e32ea from=translated src=- shape=c63348ba vocab=a94152a4
-/
@[simp] theorem principalUnitSuccQuotLift_mk
    {H : Type*} [Group H] (n : ℕ)
    (f : higherPrincipalUnitGroup F n →* H)
    (h : (higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n) ≤ f.ker)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotLift F n f h
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = f u :=
  rfl

/-- The concrete complete-DVF adjacent quotient agrees with the generic
graded-piece wrapper through explicit public equivalences.-/
def principalUnitSuccQuotEquivGradedPiece (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPiece n :=
  (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).trans
    ((AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n).trans
      (AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n (n + 1))).symm

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece F n
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPieceMk n u`.
@isnad1 id=eq.0h4v.s14.66711f49420b from=translated src=- shape=1f6501cf vocab=d97165c1
-/
@[simp] theorem principalUnitSuccQuotEquivGradedPiece_mk
    (n : ℕ) (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece F n
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPieceMk
        n u :=
  rfl

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u = 1` by the equivalent
condition `u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`.
@isnad1 id=iff.0h4v.s13.d3caa4b74e82 from=translated src=- shape=fb5a28a6 vocab=0a863520
-/
theorem principalUnitSuccQuotMk_eq_one_iff (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u = 1 ↔
      u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) := by
  change
    ((u : higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) = 1 ↔ _)
  exact QuotientGroup.eq_one_iff u

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u =
higherPrincipalUnitGroup.principalUnitSuccQuotMk F n v` by the equivalent condition `u / v ∈
(higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`.
@isnad1 id=iff.0h5v.s14.145881cb6b38 from=translated src=- shape=e0792f16 vocab=a7c1aac9
-/
theorem principalUnitSuccQuotMk_eq_iff_div_mem (n : ℕ)
    (u v : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u =
        higherPrincipalUnitGroup.principalUnitSuccQuotMk F n v ↔
      u / v ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) := by
  change
    ((u : higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) =
      (v : higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) ↔ _)
  exact QuotientGroup.eq_iff_div_mem

/--
Characterizes `u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`
by the equivalent condition `((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal
^ (n + 1)`.
@isnad1 id=iff.0h4v.s12.fa099cb34bb8 from=translated src=- shape=3b5819be vocab=da50839a
-/
theorem mem_succ_subgroupOf_iff (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) ↔
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
        F.maximalIdeal ^ (n + 1) := by
  rw [Subgroup.mem_subgroupOf, higherPrincipalUnitGroup.mem_iff]

/-- If `a ∈ m^n` with `n ≥ 1`, then `1 + a` is a unit of the valuation ring.
@isnad1 id=isunit.2h4v.s9.57c7097cd597 from=translated src=- shape=a2f87ebb vocab=7c8c0810
-/
theorem isUnit_one_add_of_mem_maximalIdeal_pow {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) : IsUnit (1 + a) := by
  have ha1 : a ∈ F.maximalIdeal := by
    have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ 1 :=
      Ideal.pow_le_pow_right hn
    simpa using hle ha
  have hnon : (-a) ∈ nonunits F.valuationSubring := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact F.maximalIdeal.neg_mem ha1
  have hunit : IsUnit (1 - (-a)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a) hnon
  simpa [sub_neg_eq_add] using hunit

/-- The unit `1 + a` attached to an element `a ∈ m^n`, for `n ≥ 1`.-/
noncomputable def principalUnitOneAddOfMemPow {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) : F.valuationSubringˣ :=
  (higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow F hn a ha).unit

/--
Establishes the identity `((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :
F.valuationSubringˣ) : F.valuationSubring) = 1 + a`.
@isnad1 id=eq.2h4v.s9.2daa1e6c2494 from=translated src=- shape=4957ed99 vocab=25d819e9
-/
@[simp] theorem principalUnitOneAddOfMemPow_val {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :
        F.valuationSubringˣ) : F.valuationSubring) =
      1 + a :=
  IsUnit.unit_spec
    (higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow F hn a ha)

/-- The unit `1 + a`, viewed as an element of `U^n`.-/
noncomputable def principalUnitOneAddOfMemPowSubgroup {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    higherPrincipalUnitGroup F n :=
  ⟨higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha, by
    rw [higherPrincipalUnitGroup.mem_iff]
    simp [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val, ha]
  ⟩

/--
Establishes the identity `((higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a ha
: higherPrincipalUnitGroup F n) : F.valuationSubringˣ) =
higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha`.
@isnad1 id=eq.2h4v.s10.3c7d24bef152 from=translated src=- shape=6b246a7d vocab=ca457360
-/
@[simp] theorem principalUnitOneAddOfMemPowSubgroup_val {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a ha :
        higherPrincipalUnitGroup F n) : F.valuationSubringˣ) =
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :=
  rfl

/-- The concrete map `m^n → U^n/U^(n+1)` sending `a` to the class of
`1 + a`.-/
noncomputable def principalUnitSuccQuotOfIdealPow (n : ℕ) (hn : 1 ≤ n) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) →
      higherPrincipalUnitGroup.principalUnitSuccQuot F n :=
  fun a =>
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
      (higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2)

/--
The defining evaluation formula for `principalUnitSuccQuotOfIdealPow` is
`higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
(higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2)`.
@isnad1 id=eq.1h4v.s13.0cde332eaef5 from=translated src=- shape=67d70b02 vocab=f1db3097
-/
@[simp] theorem principalUnitSuccQuotOfIdealPow_apply (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
      higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
        (higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2) :=
  rfl

/-- Elements of `m^(n+1)` map to the trivial class in `U^n/U^(n+1)`.
@isnad1 id=eq.2h4v.s11.0a243a154b04 from=translated src=- shape=5093c681 vocab=303d591f
-/
theorem principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
    (ha : (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a = 1 := by
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_one_iff F n _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  simp [higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup,
    higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val, ha]

/-- The map `a ↦ [1 + a]` is insensitive to changing `a` modulo `m^(n+1)`.
@isnad1 id=eq.2h5v.s11.c403c821937e from=translated src=- shape=9e767a37 vocab=84da6fd6
-/
theorem principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
    (hab : ((a : F.valuationSubring) - (b : F.valuationSubring)) ∈
      F.maximalIdeal ^ (n + 1)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn b := by
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_iff_div_mem F n _ _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  change (((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (a : F.valuationSubring) a.2 /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) ∈ F.maximalIdeal ^ (n + 1)
  rw [show (((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (a : F.valuationSubring) a.2 /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
      ((a : F.valuationSubring) - (b : F.valuationSubring)) *
        ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
          (b : F.valuationSubring) b.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
      (a : F.valuationSubring) a.2]
    have hbval :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
          F.valuationSubring) = 1 + (b : F.valuationSubring) :=
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        (b : F.valuationSubring) b.2
    have hbinv :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
          F.valuationSubring) *
          ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2)⁻¹ = 1 :=
      Units.mul_inv _
    calc
      (1 + (a : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2)⁻¹ - 1 =
          (1 + (a : F.valuationSubring)) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2)⁻¹ -
            ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
              F.valuationSubring) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2)⁻¹ := by
        rw [hbinv]
      _ = ((a : F.valuationSubring) - (b : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2)⁻¹ := by
        rw [hbval]
        ring]
  exact (F.maximalIdeal ^ (n + 1)).mul_mem_right _ hab

/-- The class `[1+a]` is trivial exactly when `a ∈ m^(n+1)`.
@isnad1 id=iff.1h4v.s11.06abd5015955 from=translated src=- shape=9722d814 vocab=303d591f
-/
theorem principalUnitSuccQuotOfIdealPow_eq_one_iff
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a = 1 ↔
      (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1) := by
  constructor
  · intro h
    have hmem :=
      (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_one_iff F n _).1 h
    rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff] at hmem
    simpa [higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val] using hmem
  · intro ha
    exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
      F n hn a ha

/-- Products of two elements of `m^n`, for `n ≥ 1`, lie in `m^(n+1)`.
@isnad1 id=mem.1h5v.s11.c573fff6e3e9 from=translated src=- shape=a4c675fb vocab=cd23bc64
-/
theorem maximalIdealPow_mul_mem_succ {n : ℕ} (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    ((a : F.valuationSubring) * (b : F.valuationSubring)) ∈
      F.maximalIdeal ^ (n + 1) := by
  have hmul :
      ((a : F.valuationSubring) * (b : F.valuationSubring)) ∈
        F.maximalIdeal ^ (n + n) := by
    simpa [pow_add] using (Ideal.mul_mem_mul a.2 b.2)
  have hle : F.maximalIdeal ^ (n + n) ≤ F.maximalIdeal ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_left hn n)
  exact hle hmul

/-- The map `a ↦ [1+a]` is additive after passing to the successive
principal-unit quotient.
@isnad1 id=eq.1h5v.s12.750aa902cef5 from=translated src=- shape=2abaf5ad vocab=69a91796
-/
theorem principalUnitSuccQuotOfIdealPow_add
    (n : ℕ) (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn (a + b) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a *
        higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn b := by
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    ← map_mul]
  symm
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_iff_div_mem F n _ _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  change ((((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (a : F.valuationSubring) a.2 *
            higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2 : F.valuationSubringˣ) /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) ∈ F.maximalIdeal ^ (n + 1)
  rw [show ((((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (a : F.valuationSubring) a.2 *
            higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2 : F.valuationSubringˣ) /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
      ((a : F.valuationSubring) * (b : F.valuationSubring)) *
        ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
          ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
            F.valuationSubring) (a + b).2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
      (a : F.valuationSubring) a.2,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        (b : F.valuationSubring) b.2]
    have habval :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
          F.valuationSubring) =
          1 + (a : F.valuationSubring) + (b : F.valuationSubring) := by
      rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring) (a + b).2]
      change 1 + ((a : F.valuationSubring) + (b : F.valuationSubring)) =
        1 + (a : F.valuationSubring) + (b : F.valuationSubring)
      ring
    have habinv :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
          F.valuationSubring) *
          ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2)⁻¹ = 1 :=
      Units.mul_inv _
    calc
      ((1 + (a : F.valuationSubring)) * (1 + (b : F.valuationSubring))) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                F.valuationSubring) (a + b).2)⁻¹ - 1 =
          ((1 + (a : F.valuationSubring)) * (1 + (b : F.valuationSubring))) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2)⁻¹ -
            ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
              F.valuationSubring) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2)⁻¹ := by
        rw [habinv]
      _ = ((a : F.valuationSubring) * (b : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                F.valuationSubring) (a + b).2)⁻¹ := by
        rw [habval]
        ring]
  exact (F.maximalIdeal ^ (n + 1)).mul_mem_right _
    (higherPrincipalUnitGroup.maximalIdealPow_mul_mem_succ F hn a b)

/-- The descent of `a ↦ [1+a]` to `m^n/m^(n+1)`.-/
noncomputable def principalUnitSuccQuotOfMaximalIdealPowSuccQuot
    (n : ℕ) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot F.toDVF n →
      higherPrincipalUnitGroup.principalUnitSuccQuot F n :=
  maximalIdealPowSuccQuotLift
    F.toDVF n
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn)
    (fun a b hsub =>
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
        F n hn a b (by simpa using hsub))

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
F n hn (maximalIdealPowSuccQuotMk F.toDVF n a) =
higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a`.
@isnad1 id=eq.1h4v.s12.019d48f00357 from=translated src=- shape=1d6f7138 vocab=1dcd1c23
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n a) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a :=
  rfl

/--
`principalUnitSuccQuotOfMaximalIdealPowSuccQuot` has the zero-value formula
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0 = 1`.
@isnad1 id=eq.1h3v.s7.c09366221c0f from=translated src=- shape=dc1b73f0 vocab=1757884c
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero
    (n : ℕ) (hn : 1 ≤ n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0 = 1 := by
  rw [← map_zero
    (maximalIdealPowSuccQuotMk F.toDVF n)]
  change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
      (maximalIdealPowSuccQuotMk F.toDVF n
        (0 : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))) = 1
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]
  exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
    F n hn (0 : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
      (F.maximalIdeal ^ (n + 1)).zero_mem

/--
`principalUnitSuccQuotOfMaximalIdealPowSuccQuot` satisfies the addition formula
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y) =
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y`.
@isnad1 id=eq.1h5v.s7.c167f53ce957 from=translated src=- shape=95487022 vocab=1e6f7539
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_add
    (n : ℕ) (hn : 1 ≤ n)
    (x y : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y := by
  refine
    MaximalIdealPowSuccQuot.inductionOn₂
      (motive := fun x' y' =>
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
            F n hn (x' + y') =
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
              F n hn x' *
            higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
              F n hn y')
      F.toDVF n x y ?_
  intro a b
  let qa :
      MaximalIdealPowSuccQuot F.toDVF n :=
    maximalIdealPowSuccQuotMk F.toDVF n a
  let qb :
      MaximalIdealPowSuccQuot F.toDVF n :=
    maximalIdealPowSuccQuotMk F.toDVF n b
  have hleft :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (qa + qb) =
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (maximalIdealPowSuccQuotMk
            F.toDVF n (a + b)) := by
    have hadd : qa + qb =
        maximalIdealPowSuccQuotMk
          F.toDVF n (a + b) := by
      exact (map_add
        (maximalIdealPowSuccQuotMk
          F.toDVF n) a b).symm
    exact congrArg
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn) hadd
  have hrep :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (maximalIdealPowSuccQuotMk
            F.toDVF n (a + b)) =
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn qa *
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn qb := by
    dsimp [qa, qb]
    change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n (a + b)) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n a) *
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n b)
    rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]
    exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_add F n hn a b
  exact hleft.trans hrep

/-- Additive form of the descended map `m^n/m^(n+1) → U^n/U^(n+1)`.-/
noncomputable def principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd
    (n : ℕ) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot F.toDVF n →+
      Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) where
  toFun x := Additive.ofMul
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x)
  map_zero' := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0) = 0
    exact congrArg Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero F n hn)
  map_add' x y := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y)) =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y)
    rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_add]

/--
The defining evaluation formula for `principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd` is
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x =
Additive.ofMul (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
x)`.
@isnad1 id=eq.1h4v.s8.31b069b85de4 from=translated src=- shape=d05030e8 vocab=6533b769
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply
    (n : ℕ) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x) :=
  rfl

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x =
1` by the equivalent condition `x = 0`.
@isnad1 id=iff.1h4v.s7.95abeb50e2e3 from=translated src=- shape=8d78489d vocab=1757884c
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
    (n : ℕ) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x = 1 ↔
      x = 0 := by
  refine
    MaximalIdealPowSuccQuot.inductionOn
      (motive := fun x' =>
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
            F n hn x' = 1 ↔ x' = 0)
      F.toDVF n x ?_
  intro a
  rw [← map_zero
    (maximalIdealPowSuccQuotMk F.toDVF n)]
  change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
      (maximalIdealPowSuccQuotMk F.toDVF n a) = 1 ↔
    (maximalIdealPowSuccQuotMk F.toDVF n a :
      MaximalIdealPowSuccQuot F.toDVF n) = 0
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
    maximalIdealPowSuccQuotMk_eq_zero_iff]
  exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_iff F n hn a

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn)`.
@isnad1 id=surjecti.1h3v.s5.c3f2c9aff94c from=translated src=- shape=b14ad41c vocab=3baa40a2
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_surjective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn) := by
  intro x
  rcases higherPrincipalUnitGroup.principalUnitSuccQuotMk_surjective F n x with ⟨u, rfl⟩
  let a0 : F.valuationSubring := ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  have ha0 : a0 ∈ F.maximalIdeal ^ n := by
    dsimp [a0]
    exact (higherPrincipalUnitGroup.mem_iff F n (u : F.valuationSubringˣ)).1 u.2
  let a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) := ⟨a0, ha0⟩
  refine ⟨maximalIdealPowSuccQuotMk F.toDVF n a, ?_⟩
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply]
  congr 1
  dsimp [a]
  apply Subtype.ext
  rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val]
  apply Units.ext
  rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val]
  dsimp [a0]
  ring

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)`.
@isnad1 id=surjecti.1h3v.s8.5a3b596cd3c6 from=translated src=- shape=ee610455 vocab=7cbe9be2
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn) := by
  intro y
  rcases higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_surjective
      F n hn (Additive.toMul y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x) = y
  rw [hx]
  rfl

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)`.
@isnad1 id=injectiv.1h3v.s8.7b2b47b7b2db from=translated src=- shape=ee610455 vocab=16010c54
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn) := by
  intro x y hxy
  have hzero :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn
        (x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_self
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd
        F n hn y)
  have hmul :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (x - y) = 1 := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (x - y)) =
      Additive.ofMul (1 : higherPrincipalUnitGroup.principalUnitSuccQuot F n) at hzero
    exact Additive.ofMul.injective hzero
  have hxmy : x - y = 0 :=
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
      F n hn (x - y)).1 hmul
  exact sub_eq_zero.mp hxmy

/-- The additive isomorphism `m^n/m^(n+1) ≃ U^n/U^(n+1)` induced by
`a ↦ 1+a`.-/
noncomputable def maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
    (n : ℕ) (hn : 1 ≤ n) :
    MaximalIdealPowSuccQuot F.toDVF n ≃+
      Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) :=
  AddEquiv.ofBijective
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)
    ⟨higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
        F n hn,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
        F n hn⟩

/--
The defining evaluation formula for `maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot` is
`higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot F n hn x =
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x`.
@isnad1 id=eq.1h4v.s9.3521878b7815 from=translated src=- shape=e5cc4e53 vocab=32925789
-/
@[simp] theorem maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply
    (n : ℕ) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
        F n hn x =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x :=
  rfl

/-- The unit-quotient coordinate theorem for a complete DVF with a specified
uniformizer: `U^n/U^(n+1)` is additively the residue field.-/
noncomputable def principalUnitSuccQuotAddEquivResidueOfUniformizer
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) ≃+ F.residueField :=
  (higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
      F n hn).symm.trans
    (residueAddEquivMaximalIdealPowSuccQuotOfUniformizer F.toDVF hpi n).symm

/-- Under the inverse of `U^n/U^(n+1) ≃ k`, the residue of `r` is represented
by the principal unit `1 + r * pi^n`.
@isnad1 id=eq.2h5v.s12.d80b7de40944 from=translated src=- shape=5d508a64 vocab=bb92d52d
-/
@[simp] theorem principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    (higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F hpi n hn).symm (F.residueMap r) =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
          (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)) := by
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer]
  rw [AddEquiv.symm_trans_apply]
  simp only [AddEquiv.symm_symm]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfUniformizer_residue]
  rw [higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply]
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply]
  change Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (maximalIdealPowSuccQuotMk F.toDVF n
          (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
        (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]

/-- The equivalence `U^n/U^(n+1) ≃ k` sends the coordinate class
`[1 + r * pi^n]` to the residue of `r`.
@isnad1 id=eq.2h5v.s12.dc2e137d5165 from=translated src=- shape=65559cf1 vocab=8b123a1a
-/
@[simp] theorem principalUnitSuccQuotAddEquivResidueOfUniformizer_coord
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F hpi n hn
        (Additive.ofMul
          (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
            (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
      F.residueMap r := by
  let E := higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
    F hpi n hn
  have hcoord :
      E.symm (F.residueMap r) =
        Additive.ofMul
          (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
            (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)) := by
    simp [E]
  change E
      (Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
          (maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    F.residueMap r
  rw [← hcoord]
  exact E.apply_symm_apply (F.residueMap r)

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
