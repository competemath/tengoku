/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.Degree
import Tengoku.LanaBelyi.Belyi.CurveField.Extension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fundamental identity for extensions of curve fields

For a finite extension `L / K` of curve fields and a place `P` of `K`,
`∑_{Q | P} e(Q|P) · f(Q|P) = [L : K]`
(`Belyi.CurveField.Place.sum_ramificationIdx_mul_inertiaDeg`), equivalently
`∑_{Q | P} e(Q|P) · deg Q = [L : K] · deg P`.

Proof: choose `t ∈ O_P` transcendental; `P` is the localisation of the chart ring
`R = A_t` at a height-one prime `𝔭`, and the places of `L` over `P` are the localisations of
the Dedekind domain `S = ` integral closure of `R` in `L` at the primes over `𝔭`. Mathlib's
fundamental identity `Ideal.sum_ramification_inertia` for `R ⊆ S` then translates, via
`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` (ramification indices) and the
degree tower `deg Q = f · deg P` (residue degrees).

## General facts

For any Dedekind domain `S` with fraction field a curve field `L` and containing `ℚ`, the
localisations at height-one primes are places (`Belyi.CurveField.Place.ofHeightOne`), the
order at such a place is the adic valuation, and the residue field is `S ⧸ w`.
-/

open IsDedekindDomain IsLocalRing Module
open scoped IntermediateField WithZero

namespace Belyi.CurveField

namespace Place

section General

variable {L : Type*} [Field L] [CharZero L]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L]
  [Algebra ℚ S] [IsScalarTower ℚ S L]

variable (S) in
theorem ratCast_mem_valuationSubringAtPrime (w : HeightOneSpectrum S) (q : ℚ) :
    (q : L) ∈ HeightOneSpectrum.valuationSubringAtPrime L w := by
  have := algebraMap_mem_valuationSubringAtPrime (K := L) w (algebraMap ℚ S q)
  rwa [← IsScalarTower.algebraMap_apply, eq_ratCast] at this

variable (L) in
/-- The place of `L` given by the localisation of `S` at a height-one prime. -/
noncomputable def ofHeightOne (w : HeightOneSpectrum S) : Place L :=
  ⟨HeightOneSpectrum.valuationSubringAtPrime L w, valuationSubringAtPrime_ne_top w,
    ratCast_mem_valuationSubringAtPrime S w⟩

theorem algebraMap_mem_ofHeightOne (w : HeightOneSpectrum S) (s : S) :
    algebraMap S L s ∈ (ofHeightOne L w).1 :=
  algebraMap_mem_valuationSubringAtPrime w s

theorem ofHeightOne_heightOneBelow (Q : Place L) (hS : ∀ s : S, algebraMap S L s ∈ Q.1) :
    ofHeightOne L (heightOneBelow Q.1 Q.ne_top hS) = Q :=
  Place.ext (valuationSubringAtPrime_heightOneBelow _ _ _)

theorem heightOneBelow_ofHeightOne (w : HeightOneSpectrum S) :
    heightOneBelow (ofHeightOne L w).1 (ofHeightOne L w).ne_top
      (algebraMap_mem_ofHeightOne w) = w :=
  heightOneBelow_valuationSubringAtPrime w

theorem algebraMap_mem_nonunits_ofHeightOne_iff (w : HeightOneSpectrum S) (s : S) :
    algebraMap S L s ∈ (ofHeightOne L w).1.nonunits ↔ s ∈ w.asIdeal := by
  conv_rhs => rw [← heightOneBelow_ofHeightOne (L := L) w]
  rw [mem_heightOneBelow]

/-- The residue map `S → κ(ofHeightOne L w)`. -/
noncomputable def heightOneResidue (w : HeightOneSpectrum S) :
    S →+* (ofHeightOne L w).ResidueField :=
  (ofHeightOne L w).residue.comp
    ((algebraMap S L).codRestrict (ofHeightOne L w).1 (algebraMap_mem_ofHeightOne w))

theorem heightOneResidue_surjective (w : HeightOneSpectrum S) :
    Function.Surjective (heightOneResidue (L := L) w) :=
  CurveField.residue_comp_surjective _ (ofHeightOne L w).ne_top _

theorem ker_heightOneResidue (w : HeightOneSpectrum S) :
    RingHom.ker (heightOneResidue (L := L) w) = w.asIdeal := by
  ext s
  rw [RingHom.mem_ker, heightOneResidue, RingHom.comp_apply, residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff, ← algebraMap_mem_nonunits_ofHeightOne_iff (L := L)]
  rfl

/-- The residue field of `ofHeightOne L w` is `S ⧸ w`. -/
noncomputable def quotientEquivResidueFieldOfHeightOne (w : HeightOneSpectrum S) :
    (S ⧸ w.asIdeal) ≃+* (ofHeightOne L w).ResidueField :=
  (Ideal.quotEquivOfEq (ker_heightOneResidue w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (heightOneResidue_surjective w))

variable [IsCurveField L]

/-- At `ofHeightOne L w`, the order is the `w`-adic valuation. -/
theorem ord_ofHeightOne (w : HeightOneSpectrum S) (x : L) :
    (ofHeightOne L w).ord x = -WithZero.log (w.valuation L x) := by
  refine (ofHeightOne L w).ord_eq_neg_log (w.valuation L) (fun y ↦ ?_)
    (HeightOneSpectrum.valuation_exists_uniformizer L w) x
  change y ∈ HeightOneSpectrum.valuationSubringAtPrime L w ↔ _
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

omit [IsCurveField L] in
theorem finrank_quotient_eq_deg_ofHeightOne (w : HeightOneSpectrum S) :
    finrank ℚ (S ⧸ w.asIdeal) = (ofHeightOne L w).deg := by
  let e : (S ⧸ w.asIdeal) ≃ₐ[ℚ] (ofHeightOne L w).ResidueField :=
    AlgEquiv.ofRingEquiv (f := quotientEquivResidueFieldOfHeightOne w)
      (fun q ↦ (quotientEquivResidueFieldOfHeightOne (L := L) w).toRingHom.map_rat_algebraMap q)
  exact e.toLinearEquiv.finrank_eq

end General

section LiesOver

/-! The following two lemmas are `IsDedekindDomain.HeightOneSpectrum.intValuation_liesOver`
and `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` from
`Mathlib.NumberTheory.RamificationInertia.Valuation`, reproved here to avoid importing the
topological prerequisites of that file. -/

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

theorem intValuation_liesOver' (x : A) :
    v.intValuation x ^ (v.asIdeal.ramificationIdx' w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hx,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity w (by simpa),
    ← Set.image_singleton, ← Ideal.map_span, WithZero.exp_neg, WithZero.exp_neg, inv_pow,
    ← WithZero.exp_nsmul, Int.nsmul_eq_mul, inv_inj, WithZero.exp_inj, ← Nat.cast_mul,
    Nat.cast_inj]
  refine multiplicity_eq_of_emultiplicity_eq_some ?_ |>.symm
  replace hx : Ideal.span {x} ≠ ⊥ := by simp [hx]
  rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible
      w.irreducible w.ne_bot,
    Nat.cast_mul, (FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

theorem valuation_liesOver' (x : K) :
    v.valuation K x ^ v.asIdeal.ramificationIdx' w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [HeightOneSpectrum.valuation_of_algebraMap, div_pow,
    ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    intValuation_liesOver' v w]

end LiesOver

section Fundamental

variable {K L : Type*} [Field K] [CharZero K] [IsCurveField K] [Field L] [CharZero L]
  [IsCurveField L] [Algebra K L] [FiniteDimensional K L]

variable (K L) in
/-- The integral closure of the chart ring `A_t` of `K` in `L` (a Dedekind domain with
fraction field `L`, finite over `A_t`). -/
abbrev chartRingExt (t : K) : Subalgebra (chartRing t) L := integralClosure (chartRing t) L

section Instances

variable (t : K) [Fact (Transcendental ℚ t)]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
instance : IsDedekindDomain (chartRingExt K L t) :=
  IsIntegralClosure.isDedekindDomain (chartRing t) K L (chartRingExt K L t)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
instance : IsFractionRing (chartRingExt K L t) L :=
  integralClosure.isFractionRing_of_finite_extension K L

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
instance : Module.Finite (chartRing t) (chartRingExt K L t) :=
  IsIntegralClosure.finite (chartRing t) K L (chartRingExt K L t)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
instance : Module.IsTorsionFree (chartRing t) (chartRingExt K L t) := inferInstance

end Instances

section Main

variable (t : K) [Fact (Transcendental ℚ t)]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
omit [IsCurveField K] [CharZero L] [IsCurveField L] [Fact (Transcendental ℚ t)] in
theorem algebraMap_chartRingExt_mem (Q : Place L) (ht : t ∈ (Q.restrict K).1)
    (s : chartRingExt K L t) : algebraMap (chartRingExt K L t) L s ∈ Q.1 := by
  have : IsIntegrallyClosedIn Q.1.toSubring L := inferInstanceAs (IsIntegrallyClosedIn Q.1 L)
  have hle : (integralClosure (chartRing t) L).toSubring ≤ Q.1.toSubring :=
    Subring.integralClosure_le_iff.mpr fun r ↦ (Q.restrict K).algebraMap_chartRing_mem t ht r
  exact hle s.2

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
omit [CharZero L] [IsCurveField L] in
theorem mem_heightOneBelow_chartRingExt_iff (Q : Place L) (ht : t ∈ (Q.restrict K).1)
    (r : chartRing t) :
    algebraMap (chartRing t) (chartRingExt K L t) r ∈
        (heightOneBelow Q.1 Q.ne_top (algebraMap_chartRingExt_mem t Q ht)).asIdeal ↔
      algebraMap (chartRing t) K r ∈ (Q.restrict K).1.nonunits := by
  rw [mem_heightOneBelow, mem_restrict_nonunits_iff]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- instance search on `integralClosure (chartRing t) L` and its quotients is slow
omit [IsCurveField L] in
theorem restrict_ofHeightOne (v : HeightOneSpectrum (chartRing t))
    (w : HeightOneSpectrum (chartRingExt K L t)) [w.asIdeal.LiesOver v.asIdeal] :
    (ofHeightOne L w).restrict K = ofChart t v := by
  set Q' := ofHeightOne L w
  have ht' : t ∈ (Q'.restrict K).1 :=
    algebraMap_mem_ofHeightOne w (algebraMap (chartRing t) (chartRingExt K L t)
      ⟨t, self_mem_chartRing t⟩)
  rw [← ofChart_toChart t (Q'.restrict K) ht']
  congr 1
  ext r
  rw [mem_toChart_iff, mem_restrict_nonunits_iff]
  change algebraMap (chartRingExt K L t) L (algebraMap (chartRing t) (chartRingExt K L t) r) ∈
    Q'.1.nonunits ↔ _
  rw [algebraMap_mem_nonunits_ofHeightOne_iff, Ideal.LiesOver.over (P := w.asIdeal)
    (p := v.asIdeal)]
  rfl

end Main

end Fundamental

end Place

end Belyi.CurveField
