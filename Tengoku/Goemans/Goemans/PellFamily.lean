/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: GPT-5.6 Sol (formalization).
-/
import Tengoku.Goemans.Goemans.Family
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Topology.Instances.Real.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# A computable integral Pell family converging to `ρ*`

Starting from `(a₀,b₀) = (3,2)`, define

`(aₙ₊₁,bₙ₊₁) = (3aₙ + 4bₙ, 2aₙ + 3bₙ)`.

These are positive Pell solutions `aₙ² - 2bₙ² = 1`, with
`1/2 < bₙ/aₙ < 1` and `bₙ/aₙ → 1/√2`.  Taking `Mₙ = n+1` produces explicit
integer members of the Proposition 4.1 family.  Their exact ratios lie in
`hStarRatios` and converge to `ρ*`; no choice of rational approximants is
involved.
-/

namespace Goemans

open Filter Real
open scoped Topology

/-! ### The Pell recurrence -/

/-- The computable pair recurrence underlying the explicit family.-/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | n + 1 =>
      let pair := pellPair n
      (3 * pair.1 + 4 * pair.2, 2 * pair.1 + 3 * pair.2)

/-- The denominator coordinate of the `n`th Pell pair.-/
def pellA (n : ℕ) : ℕ := (pellPair n).1

/-- The numerator coordinate of the `n`th Pell pair.-/
def pellB (n : ℕ) : ℕ := (pellPair n).2

/--
@isnad1 id=eq.0h0v.s3.01b77f383ba2 from=translated src=- shape=3c26ae4f vocab=4352a3e6
-/
@[simp] theorem pellA_zero : pellA 0 = 3 := rfl

/--
@isnad1 id=eq.0h0v.s3.d8b8b6d0839a from=translated src=- shape=3c26ae4f vocab=e84bd368
-/
@[simp] theorem pellB_zero : pellB 0 = 2 := rfl

/-- The first four recurrence values, including the two concrete records
checked independently in `Goemans.Family`.
@isnad1 id=and.0h0v.s6.a0c8c2405b9a from=translated src=- shape=f405d94d vocab=3283dcf5
-/
theorem pellPair_first_four :
    pellPair 0 = (3, 2) ∧
      pellPair 1 = (17, 12) ∧
      pellPair 2 = (99, 70) ∧
      pellPair 3 = (577, 408) := by
  decide

/--
@isnad1 id=eq.0h1v.s5.74a28f0a528d from=translated src=- shape=e29cd903 vocab=8db213fe
-/
@[simp] theorem pellA_succ (n : ℕ) :
    pellA (n + 1) = 3 * pellA n + 4 * pellB n := by
  simp [pellA, pellB, pellPair]

/--
@isnad1 id=eq.0h1v.s5.c20cf99d8f9a from=translated src=- shape=4e39f835 vocab=8db213fe
-/
@[simp] theorem pellB_succ (n : ℕ) :
    pellB (n + 1) = 2 * pellA n + 3 * pellB n := by
  simp [pellA, pellB, pellPair]

/-- Every Pell pair satisfies the inequalities needed by `FamilyParams`.
@isnad1 id=and.0h1v.s5.7f702e138010 from=translated src=- shape=9c27d146 vocab=6975c39f
-/
theorem pell_bounds (n : ℕ) :
    0 < pellB n ∧ pellB n < pellA n ∧ pellA n < 2 * pellB n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pellA_succ, pellB_succ]
      omega

/--
@isnad1 id=lt.0h1v.s3.692844ec5463 from=translated src=- shape=8a62b088 vocab=f508d8f9
-/
theorem pellB_pos (n : ℕ) : 0 < pellB n := (pell_bounds n).1

/--
@isnad1 id=lt.0h1v.s3.a4efb3a60f4d from=translated src=- shape=0fc427d2 vocab=b86bb684
-/
theorem pellB_lt_pellA (n : ℕ) : pellB n < pellA n := (pell_bounds n).2.1

/--
@isnad1 id=lt.0h1v.s4.6ff140bbeef6 from=translated src=- shape=ffd9fe76 vocab=6975c39f
-/
theorem pellA_lt_two_pellB (n : ℕ) : pellA n < 2 * pellB n :=
  (pell_bounds n).2.2

/--
@isnad1 id=lt.0h1v.s3.5e3575fb39f8 from=translated src=- shape=8a62b088 vocab=aa4a8c31
-/
theorem pellA_pos (n : ℕ) : 0 < pellA n :=
  (pellB_pos n).trans (pellB_lt_pellA n)

/--
@isnad1 id=le.0h1v.s3.1d8c0fdcb511 from=translated src=- shape=8a62b088 vocab=d8f2f7b6
-/
theorem one_le_pellA (n : ℕ) : 1 ≤ pellA n := by
  exact pellA_pos n

/-- The recurrence stays on the Pell conic `a² - 2b² = 1`.
@isnad1 id=eq.0h1v.s6.514f2ac88d94 from=translated src=- shape=aabec9c9 vocab=be30250f
-/
theorem pell_equation (n : ℕ) :
    pellA n ^ 2 = 2 * pellB n ^ 2 + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pellA_succ, pellB_succ]
      nlinarith

/-! ### Explicit integral family instances -/

/-- The `n`th explicit integer parameter triple, with `Mₙ = n+1`.-/
def pellFamilyParams (n : ℕ) : FamilyParams ℤ :=
  FamilyParams.ofInt (pellA n : ℤ) (pellB n : ℤ) ((n : ℤ) + 1)
    (by exact_mod_cast pellB_pos n)
    (by exact_mod_cast pellB_lt_pellA n)
    (by exact_mod_cast pellA_lt_two_pellB n)
    (by positivity)

/--
@isnad1 id=eq.0h1v.s4.115e39a350cf from=translated src=- shape=58a91df6 vocab=7d63c055
-/
@[simp] theorem pellFamilyParams_a (n : ℕ) :
    (pellFamilyParams n).a = (pellA n : ℤ) := by
  simp [pellFamilyParams]

/--
@isnad1 id=eq.0h1v.s4.7634615d3c03 from=translated src=- shape=58a91df6 vocab=737ae73f
-/
@[simp] theorem pellFamilyParams_b (n : ℕ) :
    (pellFamilyParams n).b = (pellB n : ℤ) := by
  simp [pellFamilyParams]

/--
@isnad1 id=eq.0h1v.s4.09a221ce7315 from=translated src=- shape=7125b3ab vocab=f22fed99
-/
@[simp] theorem pellFamilyParams_M (n : ℕ) :
    (pellFamilyParams n).M = (n : ℤ) + 1 := by
  simp [pellFamilyParams]

noncomputable section

/-- The `n`th genuinely integral Pell instance, cast to the real model.-/
noncomputable def pellFamilyInstance (n : ℕ) : PositiveCostInstance :=
  ⟨(pellFamilyParams n).flow.toReal, by
    rw [FamilyParams.flow_toReal]
    exact (pellFamilyParams n).toReal.flow_fcost_pos⟩

/-- Exact closed form for the ratio of the `n`th Pell instance.
@isnad1 id=eq.0h1v.s7.b8c8ec5bef91 from=translated src=- shape=cdd3b3e2 vocab=8df31f18
-/
theorem pellFamily_ratio_formula (n : ℕ) :
    (pellFamilyInstance n).ratio =
      (2 * (pellA n : ℝ) * (pellB n : ℝ) * ((n : ℝ) + 1)) /
        ((((pellA n : ℝ) ^ 2 -
              (pellA n : ℝ) * (pellB n : ℝ) +
              2 * (pellB n : ℝ) ^ 2) * ((n : ℝ) + 1)) +
          2 * (pellB n : ℝ)) := by
  rw [pellFamilyInstance, PositiveCostInstance.ratio]
  change
    (pellFamilyParams n).flow.toReal.optimalUCost /
        (pellFamilyParams n).flow.toReal.fcost = _
  rw [FamilyParams.flow_toReal]
  rw [FamilyParams.flow_optimalUCost, FamilyParams.flow_fcost]
  simp [FamilyParams.toReal]

/-- The rational slope `bₙ/aₙ` of the `n`th Pell pair.-/
def pellDelta (n : ℕ) : ℝ := (pellB n : ℝ) / (pellA n : ℝ)

/--
@isnad1 id=lt.0h1v.s3.6b8bb6cbde31 from=translated src=- shape=b9369acb vocab=c75dbaf0
-/
theorem pellDelta_pos (n : ℕ) : 0 < pellDelta n := by
  exact div_pos (by exact_mod_cast pellB_pos n)
    (by exact_mod_cast pellA_pos n)

/--
@isnad1 id=le.0h1v.s3.5c633b2b600a from=translated src=- shape=a311c14d vocab=a169d4b9
-/
theorem pellDelta_le_one (n : ℕ) : pellDelta n ≤ 1 := by
  rw [pellDelta, div_le_one (by exact_mod_cast pellA_pos n)]
  exact_mod_cast (pellB_lt_pellA n).le

/-- Ratio formula after normalizing by `aₙ² Mₙ`.
@isnad1 id=eq.0h1v.s7.f4f56951efd9 from=translated src=- shape=8882f89a vocab=15787e37
-/
theorem pellFamily_ratio_normalized (n : ℕ) :
    (pellFamilyInstance n).ratio =
      (2 * pellDelta n) /
        (1 - pellDelta n + 2 * pellDelta n ^ 2 +
          (2 * pellDelta n) / ((pellA n : ℝ) * ((n : ℝ) + 1))) := by
  rw [pellFamily_ratio_formula]
  simp only [pellDelta]
  have ha : (pellA n : ℝ) ≠ 0 := by
    exact_mod_cast (pellA_pos n).ne'
  have hM : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-! ### Direct convergence of the Pell slopes -/

/-- The contracting conjugate `3 - 2√2` of the Pell unit `3 + 2√2`.-/
def pellContraction : ℝ := 3 - 2 * Real.sqrt 2

/--
@isnad1 id=le.0h0v.s3.6d418886b39f from=translated src=- shape=ff3a10fc vocab=d6a03b14
-/
theorem pellContraction_nonneg : 0 ≤ pellContraction := by
  rw [pellContraction]
  linarith [sqrt2_lt_bound]

/--
@isnad1 id=lt.0h0v.s3.c39f3671e8c3 from=translated src=- shape=ffdda526 vocab=0260c829
-/
theorem pellContraction_lt_one : pellContraction < 1 := by
  rw [pellContraction]
  linarith [one_lt_sqrt2]

/-- Exact error formula
`aₙ - √2 bₙ = (3 - 2√2)^(n+1)`.
@isnad1 id=eq.0h1v.s5.29f10a4c34a4 from=translated src=- shape=13003081 vocab=78df2537
-/
theorem pell_error_eq_pow (n : ℕ) :
    (pellA n : ℝ) - Real.sqrt 2 * (pellB n : ℝ) =
      pellContraction ^ (n + 1) := by
  induction n with
  | zero =>
      simp [pellContraction]
      ring
  | succ n ih =>
      rw [pellA_succ, pellB_succ]
      push_cast
      calc
        3 * (pellA n : ℝ) + 4 * (pellB n : ℝ) -
              Real.sqrt 2 *
                (2 * (pellA n : ℝ) + 3 * (pellB n : ℝ)) =
            pellContraction *
              ((pellA n : ℝ) - Real.sqrt 2 * (pellB n : ℝ)) := by
                rw [pellContraction]
                nlinarith [sqrt2_mul_self]
        _ = pellContraction * pellContraction ^ (n + 1) := by rw [ih]
        _ = pellContraction ^ (n + 1 + 1) := by
          rw [pow_succ]
          ring

private theorem tendsto_pellError :
    Tendsto (fun n => pellContraction ^ (n + 1)) atTop (𝓝 0) := by
  have hpow :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      pellContraction_nonneg pellContraction_lt_one
  simpa [pow_succ] using hpow.mul_const pellContraction

private theorem tendsto_pellDeltaCorrection :
    Tendsto
      (fun n =>
        pellContraction ^ (n + 1) /
          (Real.sqrt 2 * (pellA n : ℝ)))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (g := fun n => pellContraction ^ (n + 1) / Real.sqrt 2)
  · intro n
    exact div_nonneg (pow_nonneg pellContraction_nonneg _)
      (mul_nonneg sqrt2_nonneg (by positivity))
  · intro n
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have ha : (1 : ℝ) ≤ pellA n := by exact_mod_cast one_le_pellA n
    apply div_le_div_of_nonneg_left (pow_nonneg pellContraction_nonneg _) hs
    nlinarith
  · simpa using tendsto_pellError.div_const (Real.sqrt 2)

/--
@isnad1 id=eq.0h1v.s6.b07304f3e97c from=translated src=- shape=0b35252e vocab=0689fe44
-/
theorem pellDelta_eq (n : ℕ) :
    pellDelta n =
      1 / Real.sqrt 2 -
        pellContraction ^ (n + 1) /
          (Real.sqrt 2 * (pellA n : ℝ)) := by
  rw [pellDelta]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have ha : (pellA n : ℝ) ≠ 0 := by
    exact_mod_cast (pellA_pos n).ne'
  field_simp [hs, ha]
  nlinarith [pell_error_eq_pow n]

/-- The explicit Pell slopes converge to `1/√2`.
@isnad1 id=tendsto.0h0v.s5.45e39482aac6 from=translated src=- shape=d907a9df vocab=fbf716f1
-/
theorem tendsto_pellDelta :
    Tendsto pellDelta atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hconst :
      Tendsto (fun _ : ℕ => (1 / Real.sqrt 2 : ℝ)) atTop
        (𝓝 (1 / Real.sqrt 2)) :=
    tendsto_const_nhds
  have h := hconst.sub tendsto_pellDeltaCorrection
  have h' :
      Tendsto
        (fun n =>
          1 / Real.sqrt 2 -
            pellContraction ^ (n + 1) /
              (Real.sqrt 2 * (pellA n : ℝ)))
        atTop (𝓝 (1 / Real.sqrt 2)) := by
    simpa using h
  apply h'.congr'
  filter_upwards [] with n
  rw [pellDelta_eq]

/-! ### Convergence of the exact instance ratios -/

private theorem tendsto_pellFamilyCorrection :
    Tendsto
      (fun n =>
        (2 * pellDelta n) /
          ((pellA n : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
  apply squeeze_zero (g := fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1))
  · intro n
    exact div_nonneg (mul_nonneg (by norm_num) (pellDelta_pos n).le)
      (mul_nonneg (by positivity) (by positivity))
  · intro n
    have hδle := pellDelta_le_one n
    have ha : (1 : ℝ) ≤ pellA n := by exact_mod_cast one_le_pellA n
    have hMpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply div_le_div₀ (by norm_num) (by nlinarith) hMpos
    simpa using (mul_le_mul_of_nonneg_right ha hMpos.le)
  · have hM : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hM
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    convert htwo.mul hinv using 1 <;> norm_num [div_eq_mul_inv]

private theorem pell_limit_identity :
    (2 * (1 / Real.sqrt 2)) /
        (1 - 1 / Real.sqrt 2 + 2 * (1 / Real.sqrt 2) ^ 2) =
      rhoStar := by
  rw [rhoStar]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hr : 2 * Real.sqrt 2 - 1 ≠ 0 := rhoStar_denom_pos.ne'
  have hd :
      1 - 1 / Real.sqrt 2 + 2 * (1 / Real.sqrt 2) ^ 2 ≠ 0 := by
    have hinvlt : 1 / Real.sqrt 2 < (1 : ℝ) := by
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
        one_lt_sqrt2)
    have hsquare : 0 ≤ 2 * (1 / Real.sqrt 2) ^ 2 := by positivity
    nlinarith
  apply (div_eq_iff hd).2
  field_simp [hs, hr]
  nlinarith [sqrt2_mul_self]

/-- The exact ratios of the computable integral Pell family converge to `ρ*`.
@isnad1 id=tendsto.0h0v.s4.e6417aab6869 from=translated src=- shape=b19f7695 vocab=18fc937e
-/
theorem tendsto_pellFamily_ratio :
    Tendsto (fun n => (pellFamilyInstance n).ratio) atTop (𝓝 rhoStar) := by
  let delta : ℝ := 1 / Real.sqrt 2
  have hdelta : Tendsto pellDelta atTop (𝓝 delta) := tendsto_pellDelta
  have hdenpos : 0 < 1 - delta + 2 * delta ^ 2 := by
    dsimp [delta]
    have hinvlt : 1 / Real.sqrt 2 < (1 : ℝ) := by
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
        one_lt_sqrt2)
    have hsquare : 0 ≤ 2 * (1 / Real.sqrt 2) ^ 2 := by positivity
    nlinarith
  have hnum :
      Tendsto (fun n => 2 * pellDelta n) atTop (𝓝 (2 * delta)) :=
    tendsto_const_nhds.mul hdelta
  have hden :
      Tendsto
        (fun n =>
          1 - pellDelta n + 2 * pellDelta n ^ 2 +
            (2 * pellDelta n) /
              ((pellA n : ℝ) * ((n : ℝ) + 1)))
        atTop (𝓝 (1 - delta + 2 * delta ^ 2)) := by
    simpa using
      ((tendsto_const_nhds.sub hdelta).add
        (tendsto_const_nhds.mul (hdelta.pow 2))).add
          tendsto_pellFamilyCorrection
  have hratio :
      Tendsto
        (fun n =>
          (2 * pellDelta n) /
            (1 - pellDelta n + 2 * pellDelta n ^ 2 +
              (2 * pellDelta n) /
                ((pellA n : ℝ) * ((n : ℝ) + 1))))
        atTop
        (𝓝 ((2 * delta) / (1 - delta + 2 * delta ^ 2))) :=
    hnum.div hden hdenpos.ne'
  have hlimit :
      (2 * delta) / (1 - delta + 2 * delta ^ 2) = rhoStar := by
    simpa [delta] using pell_limit_identity
  rw [hlimit] at hratio
  apply hratio.congr'
  filter_upwards [] with n
  exact (pellFamily_ratio_normalized n).symm

/--
@isnad1 id=mem.0h1v.s3.6ab189b71064 from=translated src=- shape=07d19bab vocab=136bd644
-/
theorem pellFamily_ratio_mem (n : ℕ) :
    (pellFamilyInstance n).ratio ∈ hStarRatios :=
  ⟨pellFamilyInstance n, rfl⟩

end

end Goemans
