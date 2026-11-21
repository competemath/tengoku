/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Family
import Tengoku.Seed.Algebra.Order.Ring.Unbundled.Rat
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Topology.Instances.Real.Lemmas
import Tengoku.Seed.Topology.Order.OrderClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Alternate density-based family converging to `ρ*`

This module is retained as an independent cross-check of the limiting
argument. The publication endpoint in `Goemans.Extremal` instead uses the
explicit computable Pell recurrence from `Goemans.PellFamily`; no declaration
below is on that headline proof path.

Here, rational approximants `qₙ ↑ 1/√2` provide genuine integral parameters
`aₙ = den(qₙ)`, `bₙ = num(qₙ)`, and `Mₙ = n+1`. Every resulting integer
instance is cast into the real optimization problem, and its exact ratio is
proved to converge to `ρ*`. Constructing the approximating sequence uses
`Classical.choice`, deliberately isolated in this alternate module. A shorter
real-valued specialization supplies a second check of the limiting algebra.
-/

namespace Goemans

noncomputable section

open Filter Real
open scoped Topology

private theorem half_lt_inv_sqrt_two :
    (1 : ℝ) / 2 < 1 / Real.sqrt 2 := by
  rw [lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
  nlinarith [sqrt2_lt_bound]

private theorem exists_extremalRats :
    ∃ q : ℕ → ℚ,
      (∀ n, (q n : ℝ) ∈ Set.Ioo ((1 : ℝ) / 2) (1 / Real.sqrt 2)) ∧
      Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (1 / Real.sqrt 2)) := by
  obtain ⟨q, -, hbounds, hlim⟩ :=
    Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      Rat.cast_strictMono.monotone half_lt_inv_sqrt_two
  exact ⟨q, hbounds, by simpa [Function.comp_def] using hlim⟩

/-- Rational approximants strictly between `1/2` and `1/√2`.-/
noncomputable def extremalRats : ℕ → ℚ := Classical.choose exists_extremalRats

/--
@isnad1 id=mem.0h1v.s5.a4df68529289 from=translated src=- shape=2da24e46 vocab=448777ee
-/
theorem extremalRats_bounds (n : ℕ) :
    (extremalRats n : ℝ) ∈ Set.Ioo ((1 : ℝ) / 2) (1 / Real.sqrt 2) :=
  (Classical.choose_spec exists_extremalRats).1 n

/--
@isnad1 id=tendsto.0h0v.s5.109b7d0b8d28 from=translated src=- shape=05ae7112 vocab=8c65a12c
-/
theorem tendsto_extremalRats :
    Tendsto (fun n => (extremalRats n : ℝ)) atTop
      (𝓝 (1 / Real.sqrt 2)) :=
  (Classical.choose_spec exists_extremalRats).2

private theorem den_lt_two_num_of_half_lt (q : ℚ)
    (hlo : (1 : ℝ) / 2 < (q : ℝ)) :
    (q.den : ℤ) < 2 * q.num := by
  rw [Rat.cast_def, div_eq_mul_inv] at hlo
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hlo' : (q.den : ℝ) < 2 * (q.num : ℝ) := by
    have hmul := (lt_div_iff₀ hd).mp (by simpa [div_eq_mul_inv] using hlo)
    nlinarith
  exact_mod_cast hlo'

/-- Integral family parameters obtained from the numerator and denominator of
the `n`th rational approximant.-/
def integralFamilyParams (n : ℕ) : FamilyParams ℤ := by
  let q := extremalRats n
  have hq := extremalRats_bounds n
  have hqposR : (0 : ℝ) < q := lt_trans (by norm_num) hq.1
  have hqposQ : (0 : ℚ) < q := by exact_mod_cast hqposR
  have hb : 0 < q.num := Rat.num_pos.mpr hqposQ
  have hinv_lt_one : 1 / Real.sqrt 2 < (1 : ℝ) :=
    by
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
        one_lt_sqrt2)
  have hq_lt_oneR : (q : ℝ) < 1 := hq.2.trans hinv_lt_one
  have hq_lt_oneQ : q < (1 : ℚ) := by exact_mod_cast hq_lt_oneR
  have hba : q.num < (q.den : ℤ) := Rat.num_lt_denom_iff.mpr hq_lt_oneQ
  have hab : (q.den : ℤ) < 2 * q.num := den_lt_two_num_of_half_lt q hq.1
  exact FamilyParams.ofInt (q.den : ℤ) q.num ((n : ℤ) + 1)
    hb hba hab (by positivity)

/-- The `n`th genuinely integral family member, cast into the real
optimization problem.-/
noncomputable def integralFamilyInstance (n : ℕ) : PositiveCostInstance :=
  ⟨(integralFamilyParams n).flow.toReal, by
    rw [FamilyParams.flow_toReal]
    exact (integralFamilyParams n).toReal.flow_fcost_pos⟩

/--
@isnad1 id=eq.0h1v.s4.242d10c2a308 from=translated src=- shape=2b5e007e vocab=365bf3d9
-/
@[simp] theorem integralFamilyParams_a (n : ℕ) :
    (integralFamilyParams n).a = (extremalRats n).den := by
  simp [integralFamilyParams]

/--
@isnad1 id=eq.0h1v.s3.d024ad15dbb5 from=translated src=- shape=1e5faf68 vocab=52f1e188
-/
@[simp] theorem integralFamilyParams_b (n : ℕ) :
    (integralFamilyParams n).b = (extremalRats n).num := by
  simp [integralFamilyParams]

/--
@isnad1 id=eq.0h1v.s4.b7fdd987fcf6 from=translated src=- shape=7125b3ab vocab=0a933531
-/
@[simp] theorem integralFamilyParams_M (n : ℕ) :
    (integralFamilyParams n).M = (n : ℤ) + 1 := by
  simp [integralFamilyParams]

/--
@isnad1 id=eq.0h1v.s7.b1a89b336cfe from=translated src=- shape=455f1005 vocab=09d4f9a2
-/
theorem integralFamily_ratio_formula (n : ℕ) :
    (integralFamilyInstance n).ratio =
      (2 * ((extremalRats n).den : ℝ) * ((extremalRats n).num : ℝ) *
          ((n : ℝ) + 1)) /
        (((((extremalRats n).den : ℝ) ^ 2 -
              ((extremalRats n).den : ℝ) * ((extremalRats n).num : ℝ) +
              2 * ((extremalRats n).num : ℝ) ^ 2) * ((n : ℝ) + 1)) +
          2 * ((extremalRats n).num : ℝ)) := by
  rw [integralFamilyInstance, PositiveCostInstance.ratio]
  change
    (integralFamilyParams n).flow.toReal.optimalUCost /
        (integralFamilyParams n).flow.toReal.fcost = _
  rw [FamilyParams.flow_toReal]
  rw [FamilyParams.flow_optimalUCost, FamilyParams.flow_fcost]
  simp [FamilyParams.toReal]

/--
@isnad1 id=eq.0h1v.s7.618aa25a4028 from=translated src=- shape=5229096d vocab=c29bcd62
-/
theorem integralFamily_ratio_normalized (n : ℕ) :
    (integralFamilyInstance n).ratio =
      (2 * (extremalRats n : ℝ)) /
        (1 - (extremalRats n : ℝ) + 2 * (extremalRats n : ℝ) ^ 2 +
          (2 * (extremalRats n : ℝ)) /
            (((extremalRats n).den : ℝ) * ((n : ℝ) + 1))) := by
  rw [integralFamily_ratio_formula, Rat.cast_def]
  have hd : ((extremalRats n).den : ℝ) ≠ 0 := by
    exact_mod_cast (extremalRats n).den_ne_zero
  have hM : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem tendsto_integralCorrection :
    Tendsto
      (fun n =>
        (2 * (extremalRats n : ℝ)) /
          (((extremalRats n).den : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
  apply squeeze_zero (g := fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1))
  · intro n
    exact div_nonneg (mul_nonneg (by norm_num) (by
        nlinarith [(extremalRats_bounds n).1]))
      (mul_nonneg (by positivity) (by positivity))
  · intro n
    have hδle : (extremalRats n : ℝ) ≤ 1 := by
      have hinv_lt_one : 1 / Real.sqrt 2 < (1 : ℝ) := by
        simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
          one_lt_sqrt2)
      exact (extremalRats_bounds n).2.le.trans hinv_lt_one.le
    have ha1 : (1 : ℝ) ≤ (extremalRats n).den := by
      exact_mod_cast (extremalRats n).den_pos
    have hMpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply div_le_div₀ (by norm_num) (by nlinarith) hMpos
    simpa using (mul_le_mul_of_nonneg_right ha1 hMpos.le)
  · have hM : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hM
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    convert htwo.mul hinv using 1 <;> norm_num [div_eq_mul_inv]

/-- The exact integral family ratios converge to `ρ*`.
@isnad1 id=tendsto.0h0v.s4.4ba0e92b746f from=translated src=- shape=b19f7695 vocab=151cb701
-/
theorem tendsto_integralFamily_ratio :
    Tendsto (fun n => (integralFamilyInstance n).ratio) atTop (𝓝 rhoStar) := by
  let δ : ℝ := 1 / Real.sqrt 2
  have hδ : Tendsto (fun n => (extremalRats n : ℝ)) atTop (𝓝 δ) :=
    tendsto_extremalRats
  have hδpos : 0 < δ := div_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))
  have hδlt : δ < 1 := by
    dsimp [δ]
    simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
      one_lt_sqrt2)
  have hdenpos : 0 < 1 - δ + 2 * δ ^ 2 := by positivity
  have hnum :
      Tendsto (fun n => 2 * (extremalRats n : ℝ)) atTop (𝓝 (2 * δ)) :=
    tendsto_const_nhds.mul hδ
  have hden :
      Tendsto
        (fun n =>
          1 - (extremalRats n : ℝ) + 2 * (extremalRats n : ℝ) ^ 2 +
            (2 * (extremalRats n : ℝ)) /
              (((extremalRats n).den : ℝ) * ((n : ℝ) + 1)))
        atTop (𝓝 (1 - δ + 2 * δ ^ 2)) := by
    simpa using
      ((tendsto_const_nhds.sub hδ).add
        (tendsto_const_nhds.mul (hδ.pow 2))).add tendsto_integralCorrection
  have hratio :
      Tendsto
        (fun n =>
          (2 * (extremalRats n : ℝ)) /
            (1 - (extremalRats n : ℝ) + 2 * (extremalRats n : ℝ) ^ 2 +
              (2 * (extremalRats n : ℝ)) /
                (((extremalRats n).den : ℝ) * ((n : ℝ) + 1))))
        atTop (𝓝 ((2 * δ) / (1 - δ + 2 * δ ^ 2))) :=
    hnum.div hden hdenpos.ne'
  have hlimit : (2 * δ) / (1 - δ + 2 * δ ^ 2) = rhoStar := by
    dsimp [δ]
    rw [rhoStar]
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have hr : 2 * Real.sqrt 2 - 1 ≠ 0 := rhoStar_denom_pos.ne'
    have hd :
        1 - 1 / Real.sqrt 2 + 2 * (1 / Real.sqrt 2) ^ 2 ≠ 0 := by
      positivity
    apply (div_eq_iff hd).2
    field_simp [hs, hr]
    nlinarith [sqrt2_mul_self]
  rw [hlimit] at hratio
  apply hratio.congr'
  filter_upwards [] with n
  exact (integralFamily_ratio_normalized n).symm

/--
@isnad1 id=mem.0h1v.s3.a857bffa1a97 from=translated src=- shape=07d19bab vocab=eac7fb5d
-/
theorem integralFamily_ratio_mem (n : ℕ) :
    (integralFamilyInstance n).ratio ∈ hStarRatios :=
  ⟨integralFamilyInstance n, rfl⟩

/-- A particularly simple extremizing specialization of the symbolic family.-/
def extremalFamilyParams (n : ℕ) : FamilyParams ℝ where
  a := Real.sqrt 2
  b := 1
  M := (n : ℝ) + 3
  b_pos := by norm_num
  b_lt_a := one_lt_sqrt2
  a_lt_two_b := by linarith [sqrt2_lt_bound]
  M_pos := by positivity
  gap := by
    have hδ : 0 ≤ Real.sqrt 2 - 1 := sub_nonneg.mpr one_lt_sqrt2.le
    have hM : (3 : ℝ) ≤ (n : ℝ) + 3 := by
      norm_num
    have hmul := mul_le_mul_of_nonneg_left hM hδ
    nlinarith [sqrt2_gt_bound]

/-- The positive-cost instance represented by the `n`th extremizing member.-/
def extremalFamilyInstance (n : ℕ) : PositiveCostInstance :=
  (extremalFamilyParams n).positiveFlow

/--
@isnad1 id=eq.0h1v.s7.dbf89fc62f37 from=translated src=- shape=894a14e0 vocab=1926284b
-/
theorem extremalFamily_ratio_eq (n : ℕ) :
    (extremalFamilyInstance n).ratio =
      (2 * Real.sqrt 2 * ((n : ℝ) + 3)) /
        ((4 - Real.sqrt 2) * ((n : ℝ) + 3) + 2) := by
  rw [extremalFamilyInstance, FamilyParams.positiveFlow_ratio]
  simp only [extremalFamilyParams, pow_two]
  rw [sqrt2_mul_self]
  ring

private theorem extremal_limit_identity :
    (2 * Real.sqrt 2) / (4 - Real.sqrt 2) = rhoStar := by
  rw [rhoStar]
  have h₁ : 4 - Real.sqrt 2 ≠ 0 := by
    nlinarith [sqrt2_lt_bound]
  have h₂ : 2 * Real.sqrt 2 - 1 ≠ 0 := ne_of_gt rhoStar_denom_pos
  field_simp [h₁, h₂]
  nlinarith [sqrt2_mul_self]

/-- The family ratios tend to the exact extremal constant.
@isnad1 id=tendsto.0h0v.s4.aafec0415f8c from=translated src=- shape=b19f7695 vocab=f7250100
-/
theorem tendsto_extremalFamily_ratio :
    Tendsto (fun n => (extremalFamilyInstance n).ratio) atTop (𝓝 rhoStar) := by
  have hM : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hM
  have hden : 4 - Real.sqrt 2 ≠ 0 := by
    nlinarith [sqrt2_lt_bound]
  have hnum :
      Tendsto (fun _ : ℕ => (2 * Real.sqrt 2 : ℝ)) atTop
        (𝓝 (2 * Real.sqrt 2)) :=
    tendsto_const_nhds
  have hc :
      Tendsto (fun _ : ℕ => (4 - Real.sqrt 2 : ℝ)) atTop
        (𝓝 (4 - Real.sqrt 2)) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hdenlim :
      Tendsto
        (fun n : ℕ => (4 - Real.sqrt 2) + 2 * ((n : ℝ) + 3)⁻¹)
        atTop (𝓝 (4 - Real.sqrt 2)) := by
    simpa using hc.add (htwo.mul hinv)
  have hcore :
      Tendsto
        (fun n : ℕ =>
          (2 * Real.sqrt 2) /
            ((4 - Real.sqrt 2) + 2 * ((n : ℝ) + 3)⁻¹))
        atTop (𝓝 ((2 * Real.sqrt 2) / (4 - Real.sqrt 2))) :=
    hnum.div hdenlim hden
  rw [extremal_limit_identity] at hcore
  apply hcore.congr'
  filter_upwards [] with n
  rw [extremalFamily_ratio_eq]
  have hMn : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp

/--
@isnad1 id=mem.0h1v.s3.7575614c398b from=translated src=- shape=07d19bab vocab=62bc3a32
-/
theorem extremalFamily_ratio_mem (n : ℕ) :
    (extremalFamilyInstance n).ratio ∈ hStarRatios :=
  ⟨extremalFamilyInstance n, rfl⟩

end

end Goemans
