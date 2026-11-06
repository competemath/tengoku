/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- For a normalized exponential valuation, the principal-power ideal `π^n𝒪` attached to
a normalized prime element is the `n`-th power of the positive-value maximal ideal.
@isnad1 id=eq.2h4v.s9.8d2d2919f7ea from=translated src=- shape=66cf00b1 vocab=78fc7fe1
-/
theorem uniformizerPowerIdeal_primeElement_eq_exponentialMaxIdeal_pow_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n =
      (exponentialMaxIdeal v) ^ n := by
  rw [uniformizerPowerIdeal]
  exact (exponentialMaxIdeal_pow_eq_span_primeElement_pow_of_normalized
    hv hπ n).symm

/-- The same identification, expressed using mathlib's maximal ideal of the
valuation ring.
@isnad1 id=eq.2h4v.s9.ed0200e4cd5f from=translated src=- shape=74ad5ba6 vocab=dfbbaeff
-/
theorem uniformizerPowerIdeal_primeElement_eq_maximalIdeal_pow_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n =
      (IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n := by
  rw [← exponentialMaxIdeal_eq_maximalIdeal v]
  exact uniformizerPowerIdeal_primeElement_eq_exponentialMaxIdeal_pow_of_normalized
    hv hπ n

/-- The ideal structure theorem for discrete valuation rings, successive-quotient part in
maximal-ideal notation:
`𝒪/𝔭 ≃+ 𝔭^n/𝔭^(n+1)`.  This retains the additive structure supplied by the
generic quotient-of-powers theorem instead of weakening it to a bare
bijection.-/
noncomputable def residue_addEquiv_maximalIdeal_pow_quotient
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    (exponentialValuationSubring v ⧸
      IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ≃+
      Ideal.map
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ (n + 1)))
        ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n) := by
  haveI : IsDiscreteValuationRing (exponentialValuationSubring v) :=
    normalizedExponentialValuationSubring_isDiscreteValuationRing hv hπ
  exact
    (Ideal.quotEquivPowQuotPowSucc
      (IsPrincipalIdealRing.principal
        (IsLocalRing.maximalIdeal (exponentialValuationSubring v)))
      (IsDiscreteValuationRing.not_a_field (exponentialValuationSubring v))
      n).toAddEquiv.trans
      (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow
        (IsLocalRing.maximalIdeal (exponentialValuationSubring v)) n).toAddEquiv

/-- The ideal structure theorem for discrete valuation rings, successive-quotient part in the
principal-power notation `π^n𝒪`: `𝒪/(π) ≃+ π^n𝒪/π^(n+1)𝒪`, represented as the image of `π^n𝒪`
inside `𝒪/π^(n+1)𝒪`.-/
noncomputable def residue_addEquiv_uniformizerPowerIdeal_quotient
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    (exponentialValuationSubring v ⧸
      uniformizerPowerIdeal (primeElementInValuationSubring v hπ) 1) ≃+
      Ideal.map
        (Ideal.Quotient.mk
          (uniformizerPowerIdeal (primeElementInValuationSubring v hπ) (n + 1)))
        (uniformizerPowerIdeal (primeElementInValuationSubring v hπ) n) := by
  rw [uniformizerPowerIdeal_primeElement_eq_maximalIdeal_pow_of_normalized hv hπ 1,
    pow_one,
    uniformizerPowerIdeal_primeElement_eq_maximalIdeal_pow_of_normalized hv hπ n,
    uniformizerPowerIdeal_primeElement_eq_maximalIdeal_pow_of_normalized hv hπ (n + 1)]
  exact residue_addEquiv_maximalIdeal_pow_quotient hv hπ n

/-- The graded piece `π^n𝒪 / π^{n+1}𝒪` as an additive quotient.-/
def uniformizerGradedPiece {O : Type*} [CommRing O] (π : O) (n : ℕ) : Type _ :=
  (uniformizerPowerIdeal π n) ⧸
    (Submodule.comap (uniformizerPowerIdeal π n).subtype
      (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
        Submodule O (uniformizerPowerIdeal π n))

/-- A uniformizer graded piece inherits an additive commutative group structure.-/
instance uniformizerGradedPieceAddCommGroup
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    AddCommGroup (uniformizerGradedPiece π n) := by
  change AddCommGroup
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  infer_instance

/-- A uniformizer graded piece is a module over the valuation subring.-/
instance uniformizerGradedPieceModule
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Module O (uniformizerGradedPiece π n) := by
  change Module O
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  infer_instance

/-- Explicit access to the submodule quotient implementing a uniformizer
graded piece.-/
def uniformizerGradedPieceConcreteLinearEquiv
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    uniformizerGradedPiece π n ≃ₗ[O]
      ((uniformizerPowerIdeal π n) ⧸
        (Submodule.comap (uniformizerPowerIdeal π n).subtype
          (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
            Submodule O (uniformizerPowerIdeal π n))) := by
  change
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n))) ≃ₗ[O]
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  exact LinearEquiv.refl O _

/-- The canonical class map into `π^n𝒪 / π^(n+1)𝒪`.-/
def uniformizerGradedPieceMk
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    uniformizerPowerIdeal π n →ₗ[O] uniformizerGradedPiece π n := by
  change uniformizerPowerIdeal π n →ₗ[O]
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  exact Submodule.mkQ _

/-- The concrete graded-piece equivalence sends a quotient representative to the same coset.
@isnad1 id=eq.0h4v.s12.4c29ab78c650 from=translated src=- shape=f31f2da6 vocab=215c9c28
-/
@[simp] theorem uniformizerGradedPieceConcreteLinearEquiv_mk
    {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (a : uniformizerPowerIdeal π n) :
    uniformizerGradedPieceConcreteLinearEquiv π n
        (uniformizerGradedPieceMk π n a) =
      Submodule.Quotient.mk a :=
  rfl

/-- Descend a linear map that vanishes on `π^(n+1)𝒪` inside `π^n𝒪`.-/
def uniformizerGradedPieceLinearLift
    {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (π : O) (n : ℕ)
    (f : uniformizerPowerIdeal π n →ₗ[O] M)
    (h :
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)) ≤ f.ker) :
    uniformizerGradedPiece π n →ₗ[O] M := by
  change
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n))) →ₗ[O] M
  exact
    (Submodule.comap (uniformizerPowerIdeal π n).subtype
      (uniformizerPowerIdeal π (n + 1) : Submodule O O)).liftQ f h

/-- A linear lift from the graded piece evaluates on representatives by the supplied map.
@isnad1 id=eq.1h6v.s10.c80e57991623 from=translated src=- shape=1f477516 vocab=08fc75ee
-/
@[simp] theorem uniformizerGradedPieceLinearLift_mk
    {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (π : O) (n : ℕ)
    (f : uniformizerPowerIdeal π n →ₗ[O] M)
    (h :
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)) ≤ f.ker)
    (a : uniformizerPowerIdeal π n) :
    uniformizerGradedPieceLinearLift π n f h
        (uniformizerGradedPieceMk π n a) = f a :=
  rfl

/-- The higher-unit condition `u ∈ 1 + π^n𝒪`.-/
def HigherUnit {O : Type*} [CommRing O] (π : O) (n : ℕ) (u : Oˣ) : Prop :=
  ∃ a : O, (u : O) = 1 + π ^ n * a

/-- The higher-unit condition is equivalently `u - 1 ∈ π^n𝒪`.
@isnad1 id=iff.0h4v.s6.dce0e1df53d4 from=translated src=- shape=ab313d23 vocab=9afb948f
-/
theorem higherUnit_iff_sub_one_mem_powerIdeal {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (u : Oˣ) :
    HigherUnit π n u ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
  constructor
  · rintro ⟨a, ha⟩
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
    refine ⟨a, ?_⟩
    rw [ha]
    ring
  · intro hu
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton'] at hu
    rcases hu with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + a * π ^ n := by rw [← ha]
      _ = 1 + π ^ n * a := by ring

/-- The higher unit group `U⁽ⁿ⁾ = 1 + π^n𝒪`, as an actual subgroup of `Oˣ`.-/
def higherUnitSubgroup {O : Type*} [CommRing O] (π : O) (n : ℕ) : Subgroup Oˣ where
  carrier := {u | HigherUnit π n u}
  one_mem' := by
    refine ⟨0, ?_⟩
    change (1 : O) = 1 + π ^ n * 0
    rw [mul_zero, add_zero]
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    use a + b + π ^ n * a * b
    calc
      ((u * v : Oˣ) : O) = (u : O) * (v : O) := rfl
      _ = (1 + π ^ n * a) * (1 + π ^ n * b) := by rw [ha, hb]
      _ = 1 + π ^ n * (a + b + π ^ n * a * b) := by ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    use -((u⁻¹ : Oˣ) : O) * a
    have hmul : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := Units.inv_mul u
    calc
      ((u⁻¹ : Oˣ) : O) =
          ((u⁻¹ : Oˣ) : O) * (u : O) -
            ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        ring
      _ = 1 - ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        rw [hmul]
      _ = 1 + π ^ n * (-((u⁻¹ : Oˣ) : O) * a) := by
        rw [ha]
        ring

/-- Membership in a higher-unit subgroup is characterized by proximity to one at the given level.
@isnad1 id=iff.0h4v.s6.8eff1e65f17a from=translated src=- shape=841778c8 vocab=e60bc6b5
-/
@[simp]
theorem mem_higherUnitSubgroup {O : Type*} [CommRing O]
    {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ HigherUnit π n u :=
  Iff.rfl

/-- Membership in the higher-unit subgroup is equivalently `u - 1 ∈ π^n𝒪`.
@isnad1 id=iff.0h4v.s7.fa697ab45f1a from=translated src=- shape=ba6dbc96 vocab=b9a6319e
-/
theorem mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
    {O : Type*} [CommRing O] {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
  exact Iff.trans mem_higherUnitSubgroup
    (higherUnit_iff_sub_one_mem_powerIdeal π n u)

/-- The coefficient in a higher-unit representation is unique in a domain.
@isnad1 id=eq.3h6v.s7.592e9e4efeaa from=translated src=- shape=4fc69f71 vocab=6c99e1a1
-/
theorem higherUnit_coeff_unique {O : Type*} [CommRing O] [IsDomain O]
    {π : O} {n : ℕ} (hπ0 : π ≠ 0) {u : Oˣ} {a b : O}
    (ha : (u : O) = 1 + π ^ n * a)
    (hb : (u : O) = 1 + π ^ n * b) :
    a = b := by
  have hpow : π ^ n ≠ 0 := pow_ne_zero n hπ0
  have hmul : π ^ n * a = π ^ n * b := by
    have h : 1 + π ^ n * a = 1 + π ^ n * b := by
      rw [← ha, ← hb]
    exact add_left_cancel h
  exact mul_left_cancel₀ hpow hmul

/-- A chosen coefficient `a` for an element of `U⁽ⁿ⁾ = 1 + π^n𝒪`.-/
noncomputable def chosenHigherUnitCoeff {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (u : higherUnitSubgroup π n) : O :=
  Classical.choose (show HigherUnit π n (u : Oˣ) from u.property)

/-- The chosen coefficient really represents the higher unit.
@isnad1 id=eq.0h4v.s8.da177ee3cf63 from=translated src=- shape=846ee821 vocab=a10f0117
-/
theorem chosenHigherUnitCoeff_spec {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (u : higherUnitSubgroup π n) :
    ((u : Oˣ) : O) = 1 + π ^ n * chosenHigherUnitCoeff π n u :=
  Classical.choose_spec (show HigherUnit π n (u : Oˣ) from u.property)

/-- The chosen coefficient agrees with any displayed representation.
@isnad1 id=eq.2h5v.s8.f435f61cf0a4 from=translated src=- shape=9dabc07f vocab=07506f6b
-/
theorem chosenHigherUnitCoeff_eq_of_repr {O : Type*} [CommRing O] [IsDomain O]
    {π : O} {n : ℕ} (hπ0 : π ≠ 0) {u : higherUnitSubgroup π n} {a : O}
    (ha : ((u : Oˣ) : O) = 1 + π ^ n * a) :
    chosenHigherUnitCoeff π n u = a :=
  higherUnit_coeff_unique hπ0 (chosenHigherUnitCoeff_spec π n u) ha

/-- The higher-unit filtration is decreasing for arbitrary comparable indices.
@isnad1 id=le.1h4v.s6.7be038108b11 from=translated src=- shape=1e064c51 vocab=639bc32b
-/
theorem higherUnitSubgroup_le_of_le {O : Type*} [CommRing O]
    (π : O) {m n : ℕ} (hmn : m ≤ n) :
    higherUnitSubgroup π n ≤ higherUnitSubgroup π m := by
  rintro u ⟨a, ha⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  use π ^ k * a
  calc
    (u : O) = 1 + π ^ (m + k) * a := ha
    _ = 1 + π ^ m * (π ^ k * a) := by
      rw [pow_add]
      ring

/-- In a local ring, adding an element of the maximal ideal to `1` gives a unit.
@isnad1 id=isunit.1h2v.s6.85f026f4a75b from=translated src=- shape=d3d32c99 vocab=1d23ca64
-/
theorem isUnit_one_add_of_mem_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O]
    {x : O} (hx : x ∈ IsLocalRing.maximalIdeal O) :
    IsUnit (1 + x) := by
  have hx_nonunit : x ∈ nonunits O := (IsLocalRing.mem_maximalIdeal x).mp hx
  have hneg_nonunit : -x ∈ nonunits O := by
    rw [mem_nonunits_iff] at hx_nonunit ⊢
    exact mt (fun h => (IsUnit.neg_iff x).mp h) hx_nonunit
  have hunit : IsUnit (1 - (-x)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-x) hneg_nonunit
  simpa using hunit

/-- Reduction of units modulo an ideal.-/
def unitReduction {O : Type*} [CommRing O] (I : Ideal O) : Oˣ →* (O ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

/-- Unit reduction is the residue of the underlying valuation-ring unit.
@isnad1 id=eq.0h3v.s9.739739f20a1c from=translated src=- shape=ece26442 vocab=f0c77dd4
-/
@[simp]
theorem unitReduction_apply {O : Type*} [CommRing O] (I : Ideal O) (u : Oˣ) :
    (unitReduction I u : O ⧸ I) = Ideal.Quotient.mk I (u : O) :=
  rfl

/-- The kernel of reduction modulo `π^n𝒪` is the higher unit group `1 + π^n𝒪`.
@isnad1 id=eq.0h3v.s7.00cfdbfce054 from=translated src=- shape=b256a191 vocab=06723e42
-/
theorem unitReduction_ker_powerIdeal {O : Type*} [CommRing O]
    (π : O) (n : ℕ) :
    (unitReduction (uniformizerPowerIdeal π n)).ker = higherUnitSubgroup π n := by
  ext u
  constructor
  · intro hu
    have hval :
        Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1 := by
      simpa [unitReduction] using congrArg Units.val hu
    have hmem : (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp [map_sub, hval]
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + π ^ n * a := by rw [ha]
  · rintro ⟨a, ha⟩
    rw [MonoidHom.mem_ker]
    ext
    change Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1
    rw [ha]
    rw [← (Ideal.Quotient.mk (uniformizerPowerIdeal π n)).map_one]
    apply Ideal.Quotient.eq.mpr
    have hπ : π ^ n ∈ uniformizerPowerIdeal π n :=
      Ideal.subset_span (Set.mem_singleton (π ^ n))
    simpa using (uniformizerPowerIdeal π n).mul_mem_right a hπ

/-- For a normalized exponential valuation, the kernel of reduction modulo
`maximalIdeal^n` is the higher-unit subgroup attached to a normalized prime element.
@isnad1 id=eq.2h4v.s12.dcf08eac61e9 from=translated src=- shape=835374ee vocab=8e1d7b4e
-/
theorem unitReduction_ker_maximalIdeal_pow_primeElement_of_normalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ) :
    (unitReduction
      ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n)).ker =
      higherUnitSubgroup (primeElementInValuationSubring v hπ) n := by
  rw [← uniformizerPowerIdeal_primeElement_eq_maximalIdeal_pow_of_normalized hv hπ n]
  exact unitReduction_ker_powerIdeal (primeElementInValuationSubring v hπ) n

/-- A local quotient map induces a surjection on unit groups.
@isnad1 id=surjecti.0h2v.s9.005e06dfe5e8 from=translated src=- shape=2574f916 vocab=c3e132c5
-/
theorem unitReduction_surjective_of_isLocalHom {O : Type*} [CommRing O]
    (I : Ideal O) [IsLocalHom (Ideal.Quotient.mk I)] :
    Function.Surjective (unitReduction I) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective inferInstance

/-- For a exponential valuation ring, the quotient map modulo
`maximalIdeal^n` is local for `n ≥ 1`.
@isnad1 id=islocalh.1h3v.s13.faa19ad44323 from=translated src=- shape=abee52cf vocab=698f6ab8
-/
theorem unitReduction_isLocalHom_maximalIdeal_pow_of_pos
    {K : Type*} [Field K] (v : ExponentialValuation K)
    {n : ℕ} (hn : 1 ≤ n) :
    IsLocalHom
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n)) := by
  have hn0 : n ≠ 0 := by
    omega
  have hpow_le :
      (IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n ≤
        IsLocalRing.maximalIdeal (exponentialValuationSubring v) :=
    Ideal.pow_le_self hn0
  exact
    isLocalHom_of_le_jacobson_bot
      ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n)
      (hpow_le.trans
        (IsLocalRing.maximalIdeal_le_jacobson
          (⊥ : Ideal (exponentialValuationSubring v))))

/-- The first-isomorphism-theorem form of the unit quotient modulo `π^n𝒪`.-/
noncomputable def unitsModPowerIdealEquivOfSurjective {O : Type*} [CommRing O]
    (π : O) (n : ℕ)
    (hsurj : Function.Surjective (unitReduction (uniformizerPowerIdeal π n))) :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
      (unitReduction_ker_powerIdeal π n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (unitReduction (uniformizerPowerIdeal π n)) hsurj)

/-- If reduction modulo `π^n𝒪` is a local quotient, then
`Oˣ/U⁽ⁿ⁾` is the unit group of `O/π^n𝒪`.-/
noncomputable def unitsModPowerIdealEquivOfIsLocalHom {O : Type*} [CommRing O]
    (π : O) (n : ℕ) [IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n))] :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ :=
  unitsModPowerIdealEquivOfSurjective π n
    (unitReduction_surjective_of_isLocalHom (uniformizerPowerIdeal π n))

/-- The first-isomorphism-theorem form for a normalized exponential-valuation ring,
modulo `maximalIdeal^n`, assuming surjectivity of reduction on units.-/
noncomputable def unitsModMaximalIdealPowEquivOfSurjectiveNormalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) (n : ℕ)
    (hsurj : Function.Surjective
      (unitReduction
        ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n))) :
    ((exponentialValuationSubring v)ˣ ⧸
        higherUnitSubgroup (primeElementInValuationSubring v hπ) n) ≃*
      (exponentialValuationSubring v ⧸
        (IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
      (unitReduction_ker_maximalIdeal_pow_primeElement_of_normalized
        hv hπ n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (unitReduction
        ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n))
      hsurj)

/-- For a normalized exponential-valuation ring and `n ≥ 1`,
`Oˣ/U⁽ⁿ⁾` is the unit group of `O/maximalIdeal^n`.-/
noncomputable def unitsModMaximalIdealPowEquivOfNormalized
    {K : Type*} [Field K] {v : ExponentialValuation K}
    (hv : NormalizedExponentialValuation v) {π : K}
    (hπ : PrimeElementFor v π) {n : ℕ} (hn : 1 ≤ n) :
    ((exponentialValuationSubring v)ˣ ⧸
        higherUnitSubgroup (primeElementInValuationSubring v hπ) n) ≃*
      (exponentialValuationSubring v ⧸
        (IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n)ˣ := by
  letI : IsLocalHom
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n)) :=
    unitReduction_isLocalHom_maximalIdeal_pow_of_pos v hn
  exact unitsModMaximalIdealPowEquivOfSurjectiveNormalized hv hπ n
    (unitReduction_surjective_of_isLocalHom
      ((IsLocalRing.maximalIdeal (exponentialValuationSubring v)) ^ n))

/-- For `n ≥ 1`, the ideal `π^n𝒪` is contained in `(π)`.
@isnad1 id=le.1h3v.s6.d34a60b5561e from=translated src=- shape=986a2197 vocab=ed874538
-/
theorem uniformizerPowerIdeal_le_span_singleton {O : Type*} [CommRing O]
    {π : O} {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.span ({π} : Set O) := by
  cases n with
  | zero => cases hn
  | succ n =>
      rw [uniformizerPowerIdeal, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨π ^ n, by simp [pow_succ, mul_comm]⟩

/-- In a DVR, `π^n𝒪` lies in the Jacobson radical for `n ≥ 1` and `π` irreducible.
@isnad1 id=le.2h3v.s7.11ffc0cae759 from=translated src=- shape=3f548e43 vocab=4cecdece
-/
theorem uniformizerPowerIdeal_le_jacobson_bot {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.jacobson (⊥ : Ideal O) := by
  have hmax : (Ideal.span ({π} : Set O)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hπ
  have hspan : Ideal.span ({π} : Set O) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  exact (uniformizerPowerIdeal_le_span_singleton (π := π) hn).trans
    (by rw [hspan]; exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal O))

/-- The quotient map modulo `π^n𝒪` is local in a DVR, for `n ≥ 1`.
@isnad1 id=islocalh.2h3v.s8.b9c6bdfc9693 from=translated src=- shape=b988c860 vocab=3a3822e4
-/
theorem unitReduction_isLocalHom_of_dvr {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n)) :=
  isLocalHom_of_le_jacobson_bot (uniformizerPowerIdeal π n)
    (uniformizerPowerIdeal_le_jacobson_bot hπ hn)

/-- The graded coefficient map `U⁽ⁿ⁾ → 𝒪/(π)`, `1 + π^n a ↦ a mod π`,
viewed multiplicatively by tagging the additive residue group as `Multiplicative`.-/
noncomputable def higherUnitCoeffModHom {O : Type*}
    [CommRing O] [IsDomain O] {π : O} (hπ0 : π ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    higherUnitSubgroup π n →*
      Multiplicative (O ⧸ Ideal.span ({π} : Set O)) where
  toFun u :=
    Multiplicative.ofAdd
      (Ideal.Quotient.mk (Ideal.span ({π} : Set O)) (chosenHigherUnitCoeff π n u))
  map_one' := by
    apply Multiplicative.ofAdd.injective
    change Ideal.Quotient.mk (Ideal.span ({π} : Set O))
        (chosenHigherUnitCoeff π n (1 : higherUnitSubgroup π n)) = 0
    have hcoeff :
        chosenHigherUnitCoeff π n (1 : higherUnitSubgroup π n) = 0 := by
      apply chosenHigherUnitCoeff_eq_of_repr hπ0
      change (1 : O) = 1 + π ^ n * 0
      rw [mul_zero, add_zero]
    rw [hcoeff, map_zero]
  map_mul' u v := by
    apply Multiplicative.ofAdd.injective
    let I : Ideal O := Ideal.span ({π} : Set O)
    let cu : O := chosenHigherUnitCoeff π n u
    let cv : O := chosenHigherUnitCoeff π n v
    let cuv : O := chosenHigherUnitCoeff π n (u * v)
    have hu : ((u : Oˣ) : O) = 1 + π ^ n * cu :=
      chosenHigherUnitCoeff_spec π n u
    have hv : ((v : Oˣ) : O) = 1 + π ^ n * cv :=
      chosenHigherUnitCoeff_spec π n v
    have hrepr : (((u * v : higherUnitSubgroup π n) : Oˣ) : O) =
        1 + π ^ n * (cu + cv + π ^ n * cu * cv) := by
      calc
        (((u * v : higherUnitSubgroup π n) : Oˣ) : O) =
            ((u : Oˣ) : O) * ((v : Oˣ) : O) := rfl
        _ = (1 + π ^ n * cu) * (1 + π ^ n * cv) := by rw [hu, hv]
        _ = 1 + π ^ n * (cu + cv + π ^ n * cu * cv) := by ring
    have hcuv : cuv = cu + cv + π ^ n * cu * cv :=
      chosenHigherUnitCoeff_eq_of_repr hπ0 hrepr
    change Ideal.Quotient.mk I cuv =
      Ideal.Quotient.mk I cu + Ideal.Quotient.mk I cv
    rw [hcuv]
    change Ideal.Quotient.mk I (cu + cv + π ^ n * cu * cv) =
      Ideal.Quotient.mk I (cu + cv)
    apply Ideal.Quotient.eq.mpr
    have hpow_mem : π ^ n * cu * cv ∈ I := by
      have hbase : π ^ n ∈ uniformizerPowerIdeal π n :=
        Ideal.subset_span (Set.mem_singleton (π ^ n))
      have hmem' : π ^ n * (cu * cv) ∈ I :=
        uniformizerPowerIdeal_le_span_singleton (π := π) hn
          ((uniformizerPowerIdeal π n).mul_mem_right (cu * cv) hbase)
      simpa [mul_assoc] using hmem'
    have hdiff : (cu + cv + π ^ n * cu * cv) - (cu + cv) = π ^ n * cu * cv := by
      ring
    simpa [I, hdiff]
      using hpow_mem

/-- The kernel of the coefficient map is `U⁽ⁿ⁺¹⁾`.
@isnad1 id=eq.2h3v.s9.438d620bb2d7 from=translated src=- shape=3c89c4f6 vocab=4a9fa918
-/
theorem higherUnitCoeffModHom_ker {O : Type*}
    [CommRing O] [IsDomain O] {π : O} (hπ0 : π ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (higherUnitCoeffModHom (O := O) hπ0 n hn).ker =
      Subgroup.comap (higherUnitSubgroup π n).subtype
        (higherUnitSubgroup π (n + 1)) := by
  ext u
  constructor
  · intro hu
    have hzero :
        Ideal.Quotient.mk (Ideal.span ({π} : Set O)) (chosenHigherUnitCoeff π n u) = 0 := by
      simpa [higherUnitCoeffModHom] using congrArg Multiplicative.toAdd hu
    have hmem : chosenHigherUnitCoeff π n u ∈ Ideal.span ({π} : Set O) := by
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨b, hb⟩
    change (u : Oˣ) ∈ higherUnitSubgroup π (n + 1)
    use b
    calc
      ((u : Oˣ) : O) = 1 + π ^ n * chosenHigherUnitCoeff π n u :=
        chosenHigherUnitCoeff_spec π n u
      _ = 1 + π ^ (n + 1) * b := by
        rw [hb]
        rw [pow_succ']
        ring
  · intro hu
    rw [MonoidHom.mem_ker]
    apply Multiplicative.ofAdd.injective
    change Ideal.Quotient.mk (Ideal.span ({π} : Set O)) (chosenHigherUnitCoeff π n u) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    change (u : Oˣ) ∈ higherUnitSubgroup π (n + 1) at hu
    rcases hu with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply chosenHigherUnitCoeff_eq_of_repr hπ0
    calc
      ((u : Oˣ) : O) = 1 + π ^ (n + 1) * b := hb
      _ = 1 + π ^ n * (π * b) := by
        rw [pow_succ']
        ring

/-- The coefficient map `U⁽ⁿ⁾ → 𝒪/(π)` is surjective.
@isnad1 id=surjecti.2h3v.s10.e797204ed067 from=translated src=- shape=613b6edc vocab=92189da3
-/
theorem higherUnitCoeffModHom_surjective {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (higherUnitCoeffModHom (O := O) hπ.ne_zero n hn) := by
  intro y
  refine Multiplicative.rec ?_ y
  intro yadd
  refine Quotient.inductionOn yadd ?_
  intro a
  have hx_mem : π ^ n * a ∈ IsLocalRing.maximalIdeal O := by
    rw [hπ.maximalIdeal_eq]
    have hbase : π ^ n ∈ uniformizerPowerIdeal π n :=
      Ideal.subset_span (Set.mem_singleton (π ^ n))
    exact uniformizerPowerIdeal_le_span_singleton (π := π) hn
      ((uniformizerPowerIdeal π n).mul_mem_right a hbase)
  have hunit : IsUnit (1 + π ^ n * a) :=
    isUnit_one_add_of_mem_maximalIdeal hx_mem
  let u0 : Oˣ := hunit.unit
  have hu0 : (u0 : O) = 1 + π ^ n * a := hunit.unit_spec
  let u : higherUnitSubgroup π n :=
    ⟨u0, ⟨a, hu0⟩⟩
  refine ⟨u, ?_⟩
  apply Multiplicative.ofAdd.injective
  change Ideal.Quotient.mk (Ideal.span ({π} : Set O)) (chosenHigherUnitCoeff π n u) =
    Ideal.Quotient.mk (Ideal.span ({π} : Set O)) a
  rw [chosenHigherUnitCoeff_eq_of_repr hπ.ne_zero]
  exact hu0

/-- The explicit higher unit `1 + π^n a`, for `n ≥ 1` in a DVR.-/
noncomputable def higherUnitOneAdd {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) (a : O) :
    higherUnitSubgroup π n :=
  let hmem : π ^ n * a ∈ IsLocalRing.maximalIdeal O := by
    rw [hπ.maximalIdeal_eq]
    have hbase : π ^ n ∈ uniformizerPowerIdeal π n :=
      Ideal.subset_span (Set.mem_singleton (π ^ n))
    exact uniformizerPowerIdeal_le_span_singleton (π := π) hn
      ((uniformizerPowerIdeal π n).mul_mem_right a hbase)
  let hunit : IsUnit (1 + π ^ n * a) :=
    isUnit_one_add_of_mem_maximalIdeal hmem
  ⟨hunit.unit, ⟨a, hunit.unit_spec⟩⟩

/-- The multiplicative first-isomorphism-theorem form of
`U⁽ⁿ⁾/U⁽ⁿ⁺¹⁾ ≃ 𝒪/(π)`.-/
noncomputable def higherUnitGradedPieceMulEquivResidue {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    ((higherUnitSubgroup π n) ⧸
      Subgroup.comap (higherUnitSubgroup π n).subtype
        (higherUnitSubgroup π (n + 1))) ≃*
      Multiplicative (O ⧸ Ideal.span ({π} : Set O)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (higherUnitCoeffModHom_ker (O := O) hπ.ne_zero n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (higherUnitCoeffModHom (O := O) hπ.ne_zero n hn)
      (higherUnitCoeffModHom_surjective hπ n hn))

/-- The unit-reduction and graded-piece equivalences, surjectivity part for the reduction map on
unit groups.
@isnad1 id=surjecti.2h3v.s8.3a54e93dfa6b from=translated src=- shape=74f7dccd vocab=cc4041de
-/
theorem units_reduction_surjective
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (unitReduction (uniformizerPowerIdeal π n)) := by
  let : IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n)) :=
    unitReduction_isLocalHom_of_dvr hπ hn
  exact unitReduction_surjective_of_isLocalHom (uniformizerPowerIdeal π n)

/-- The unit-reduction and graded-piece equivalences, the named first-isomorphism-theorem
equivalence
`Oˣ/U⁽ⁿ⁾ ≃ (O/π^nO)ˣ`.-/
noncomputable def units_quotient_equiv
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ := by
  exact unitsModPowerIdealEquivOfSurjective π n
    (units_reduction_surjective hπ hn)

/-- The unit-quotient equivalence of the unit-reduction and graded-piece equivalences is induced by
reduction modulo `πⁿO`.
@isnad1 id=eq.2h4v.s11.2c250ad2ae28 from=translated src=- shape=ec7e185f vocab=429d79b4
-/
@[simp]
theorem units_quotient_equiv_mk
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) (u : Oˣ) :
    units_quotient_equiv hπ hn (QuotientGroup.mk u) =
      unitReduction (uniformizerPowerIdeal π n) u := by
  change QuotientGroup.kerLift (unitReduction (uniformizerPowerIdeal π n))
      ((QuotientGroup.quotientMulEquivOfEq
        (unitReduction_ker_powerIdeal π n).symm) (QuotientGroup.mk u)) =
    unitReduction (uniformizerPowerIdeal π n) u
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (unitReduction (uniformizerPowerIdeal π n)) u

/-- The unit-reduction and graded-piece equivalences, the named additive graded-piece equivalence
`U⁽ⁿ⁾/U⁽ⁿ⁺¹⁾ ≃+ O/(π)`.-/
noncomputable def higher_unit_graded_equiv
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Additive
      ((higherUnitSubgroup π n) ⧸
        Subgroup.comap (higherUnitSubgroup π n).subtype
          (higherUnitSubgroup π (n + 1))) ≃+
      (O ⧸ Ideal.span ({π} : Set O)) :=
  MulEquiv.toAdditiveLeft
    (higherUnitGradedPieceMulEquivResidue hπ n hn)

end Valuations
end LubinTate

end
