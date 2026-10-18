/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.ZerosPoles
import Tengoku.LanaBelyi.Belyi.CurveField.Residue
import Tengoku.Seed.NumberTheory.RamificationInertia.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The degree of the divisor of zeros (and of poles) of a function

For `t` in a curve field `K`, transcendental over `ℚ`,
`∑_{P, ord_P t > 0} ord_P(t) · deg P = [K : ℚ(t)]` and likewise for the poles
(`Belyi.CurveField.Place.sum_ord_mul_deg_zeros`, `Belyi.CurveField.Place.sum_ord_mul_deg_poles`).

This is the fundamental identity `∑ e f = [L : K]` for the Dedekind extension
`ℚ[t] ⊆ A_t` at the prime `(t)` (Mathlib's `Ideal.sum_ramification_inertia`), translated to
places via the chart description: at a place `P = ofChart t v`, the order `ord_P` is the
`v`-adic valuation (`Belyi.CurveField.Place.ord_ofChart`), and `κ(P) ≅ A_t ⧸ v`
(`Belyi.CurveField.Place.quotientEquivResidueField`).

## Main results

* `Belyi.CurveField.Place.ord_eq_neg_log`: `ord_P` is the unique normalised valuation with
  valuation ring `O_P`.
* `Belyi.CurveField.Place.ord_ofChart`, `Belyi.CurveField.Place.ord_ofChart_algebraMap`.
* `Belyi.CurveField.Place.finrank_quotient_eq_deg`: `[A_t ⧸ v : ℚ] = deg (ofChart t v)`.
* `Belyi.CurveField.Place.sum_ord_mul_deg_zeros`, `Belyi.CurveField.Place.sum_ord_mul_deg_poles`.
-/

open IsDedekindDomain IsLocalRing Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin WithZero

namespace Belyi.CurveField.Place

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

section Normalised

variable (P : Place K) (w : Valuation K ℤᵐ⁰) (hw : ∀ x, x ∈ P.1 ↔ w x ≤ 1)
include hw

theorem ord_eq_zero_of_valuation_eq_one {y : K} (hy : w y = 1) : P.ord y = 0 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  refine (P.ord_eq_zero_iff hy0).mpr ⟨(hw y).mpr hy.le, (hw _).mpr ?_⟩
  rw [map_inv₀, hy, inv_one]

/-- `ord_P` is the unique normalised discrete valuation with valuation ring `O_P`. -/
theorem ord_eq_neg_log (hπ : ∃ π, w π = WithZero.exp (-1)) (x : K) :
    P.ord x = -WithZero.log (w x) := by
  obtain ⟨π, hπ⟩ := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  -- the order of `π` is `1`
  have hm : P.ord π = 1 := by
    have hpos : 0 < P.ord π := by
      have hmem : π ∈ P.1 := (hw π).mpr (by rw [hπ]; decide)
      have hinv : π⁻¹ ∉ P.1 := by
        rw [hw, map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]; decide
      have h0 := P.ord_nonneg_of_mem hmem
      rcases h0.lt_or_eq with h | h
      · exact h
      · exact absurd ((P.ord_eq_zero_iff hπ0).mp h.symm).2 hinv
    obtain ⟨ϖ, hϖ⟩ := P.exists_ord_eq_one
    have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
    set k := WithZero.log (w ϖ)
    have hwϖ : w ϖ = WithZero.exp k := (WithZero.exp_log (by simpa using hϖ0)).symm
    have hy : w (ϖ * π ^ k) = 1 := by
      rw [map_mul, map_zpow₀, hwϖ, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    have := P.ord_eq_zero_of_valuation_eq_one w hw hy
    rw [P.ord_mul hϖ0 (zpow_ne_zero _ hπ0), ord_zpow, hϖ] at this
    have hkm : (-k) * P.ord π = 1 := by linarith
    exact Int.eq_one_of_mul_eq_one_left hpos.le hkm
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  set n := WithZero.log (w x)
  have hwx : w x = WithZero.exp n := (WithZero.exp_log (by simpa using hx0)).symm
  have hy : w (x * π ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hwx, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have := P.ord_eq_zero_of_valuation_eq_one w hw hy
  rw [P.ord_mul hx0 (zpow_ne_zero _ hπ0), ord_zpow, hm] at this
  linarith

end Normalised

section Chart

variable (t : K) [Fact (Transcendental ℚ t)]

/-- At the place attached to a height-one prime `v` of the chart ring, `ord` is the `v`-adic
valuation. -/
theorem ord_ofChart (v : HeightOneSpectrum (chartRing t)) (x : K) :
    (ofChart t v).ord x = -WithZero.log (v.valuation K x) := by
  refine (ofChart t v).ord_eq_neg_log (v.valuation K) (fun y ↦ ?_)
    (HeightOneSpectrum.valuation_exists_uniformizer K v) x
  rw [ofChart_val, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

theorem ord_ofChart_algebraMap (v : HeightOneSpectrum (chartRing t)) {r : chartRing t}
    (hr : r ≠ 0) :
    (ofChart t v).ord (algebraMap (chartRing t) K r) =
      multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [ord_ofChart, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hr, WithZero.log_exp, neg_neg]

/-- The residue map of the chart ring onto the residue field of `ofChart t v`. -/
noncomputable def chartResidue (v : HeightOneSpectrum (chartRing t)) :
    chartRing t →+* (ofChart t v).ResidueField :=
  (ofChart t v).residue.comp ((algebraMap (chartRing t) K).codRestrict
    (ofChart t v).1 ((ofChart t v).algebraMap_chartRing_mem t (self_mem_ofChart t v)))

theorem chartResidue_surjective (v : HeightOneSpectrum (chartRing t)) :
    Function.Surjective (chartResidue t v) :=
  (ofChart t v).residue_comp_surjective t (self_mem_ofChart t v)

theorem ker_chartResidue (v : HeightOneSpectrum (chartRing t)) :
    RingHom.ker (chartResidue t v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, chartResidue, RingHom.comp_apply, residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  conv_rhs => rw [← toChart_ofChart t v]
  rw [mem_toChart_iff]
  rfl

/-- The residue field of the place attached to `v` is `A_t ⧸ v`. -/
noncomputable def quotientEquivResidueField (v : HeightOneSpectrum (chartRing t)) :
    (chartRing t ⧸ v.asIdeal) ≃+* (ofChart t v).ResidueField :=
  (Ideal.quotEquivOfEq (ker_chartResidue t v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (chartResidue_surjective t v))

theorem finrank_quotient_eq_deg (v : HeightOneSpectrum (chartRing t)) :
    Module.finrank ℚ (chartRing t ⧸ v.asIdeal) = (ofChart t v).deg := by
  let e : (chartRing t ⧸ v.asIdeal) ≃ₐ[ℚ] (ofChart t v).ResidueField :=
    AlgEquiv.ofRingEquiv (f := quotientEquivResidueField t v)
      (fun q ↦ (quotientEquivResidueField t v).toRingHom.map_rat_algebraMap q)
  exact e.toLinearEquiv.finrank_eq

end Chart

section Zeros

variable (t : K) [Fact (Transcendental ℚ t)]

/-- `t` as an element of `ℚ[t]`. -/
private noncomputable def tR : Algebra.adjoin ℚ {t} := ⟨t, Algebra.self_mem_adjoin_singleton ℚ t⟩

/-- `t` as an element of the chart ring `A_t`. -/
private noncomputable def tS : chartRing t := algebraMap (Algebra.adjoin ℚ {t}) (chartRing t) (tR t)

end Zeros

end Belyi.CurveField.Place

namespace Belyi.CurveField

theorem adjoin_inv_eq {K : Type*} [Field K] [CharZero K] (t : K) : ℚ⟮t⁻¹⟯ = ℚ⟮t⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self ℚ t⁻¹)

namespace Place

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

end Place

end Belyi.CurveField
