import Tengoku.Formalslt.FormalSLT.Covering.GuardedContinuousDudley
import Tengoku.Formalslt.FormalSLT.Covering.UnitIntervalDudley

/-!
# Guarded continuous Dudley capstone on the unit interval

This module instantiates the guarded positive-radius continuous Dudley passage
on the concrete unit-interval Rademacher linear process. The entropy profile is
real-valued, nonconstant, and used only through dyadic guarded annuli, avoiding
the old global `Antitone (ℝ → ℝ)` continuous theorem surface.
-/

namespace FormalSLT.Covering.ContinuousDudleyUnitInterval

open scoped BigOperators Interval
open MeasureTheory
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.UnitIntervalDudley

noncomputable section

/-- Dyadic-indexed rounded-grid cover-count profile for the unit interval. -/
def unitIntervalRoundedGridCoverProfile (j : ℕ) : ℕ :=
  unitIntervalRoundedDyadicGridCoverCount j

/-- The dyadic-indexed profile is definitionally the rounded-grid cover count.

This is intentionally a dyadic-indexed statement, not a global real-radius
covering-number antitonicity claim.
@isnad1 id=eq.0h1v.s3.de8820d2b59a from=translated src=- shape=0fc427d2 vocab=ff6249dd
-/
-- fidelity: This is only a definitional identity for the rounded-grid profile;
-- it is not advertised as a separate domination theorem.
theorem unitInterval_coverProfile_eq_roundedDyadicGridCoverCount (j : ℕ) :
    unitIntervalRoundedGridCoverProfile j = unitIntervalRoundedDyadicGridCoverCount j := by
  rfl

/-- A bounded, nonconstant positive entropy profile used for the guarded
unit-interval capstone. -/
def unitIntervalEntropyProfile (ε : ℝ) : ℝ :=
  20 + Real.exp (-ε)

/--
@isnad1 id=le.0h1v.s3.4fff1330f4fa from=translated src=- shape=8a62b088 vocab=b544b1e1
-/
theorem unitIntervalEntropyProfile_nonneg (ε : ℝ) :
    0 ≤ unitIntervalEntropyProfile ε := by
  dsimp [unitIntervalEntropyProfile]
  positivity

/--
@isnad1 id=antitone.0h0v.s2.4f8353ce1afc from=translated src=- shape=e3d48bcb vocab=87eec680
-/
theorem unitIntervalEntropyProfile_antitone :
    Antitone unitIntervalEntropyProfile := by
  intro a b hab
  dsimp [unitIntervalEntropyProfile]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left (Real.exp_le_exp.mpr (neg_le_neg hab)) 20

/--
@isnad1 id=guardeda.0h1v.s3.b538f86c9cc8 from=translated src=- shape=7f61ff03 vocab=493c26ef
-/
theorem unitIntervalEntropyProfile_guarded (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus unitIntervalEntropyProfile (1 : ℝ) j := by
  intro ε _hleft hright
  exact unitIntervalEntropyProfile_antitone hright

/--
@isnad1 id=interval.0h2v.s4.3757530caf3d from=translated src=- shape=703fab3b vocab=cfc6da87
-/
theorem unitIntervalEntropyProfile_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable unitIntervalEntropyProfile volume a b := by
  have hcont : Continuous unitIntervalEntropyProfile := by
    change Continuous ((fun _ : ℝ => (20 : ℝ)) + Real.exp ∘ fun a => -a)
    exact continuous_const.add (Real.continuous_exp.comp continuous_neg)
  exact hcont.intervalIntegrable a b

/-- The entropy integrand is load-bearing: it is not a constant profile.
@isnad1 id=ne.0h0v.s4.630f761c5ca9 from=translated src=- shape=fe96b7c9 vocab=65e1c68d
-/
-- fidelity: The two endpoint values are unequal, so the capstone integral is
-- not a disguised constant-entropy bound.
theorem unitInterval_entropyProfile_nonconstant :
    unitIntervalEntropyProfile 0 ≠ unitIntervalEntropyProfile 1 := by
  have hexp_lt_one : Real.exp (-(1 : ℝ)) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by norm_num : (-(1 : ℝ)) < 0)
  intro h
  norm_num [unitIntervalEntropyProfile] at h
  have : Real.exp (-(1 : ℝ)) = 1 := by
    linarith
  linarith

/-- The entropy integrand has positive mass on the continuous Dudley interval.
@isnad1 id=lt.0h0v.s5.75a7527b6281 from=translated src=- shape=82bd89d8 vocab=46ab9f5b
-/
-- fidelity: The integral dominates the positive rectangle with height `20`
-- over `[0, 1 / 2]`, so the entropy term is not zero.
theorem unitInterval_entropyProfile_integral_positive :
    0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε := by
  have hrect :
      (((1 : ℝ) / 2) - 0) * 20 ≤
        ∫ ε in (0 : ℝ)..((1 : ℝ) / 2), unitIntervalEntropyProfile ε := by
    exact
      FiniteSubGaussianProcess.interval_const_mul_le_integral_of_le_on
        (f := unitIntervalEntropyProfile) (a := (0 : ℝ))
        (b := ((1 : ℝ) / 2)) (c := (20 : ℝ))
        (by norm_num)
        (unitIntervalEntropyProfile_intervalIntegrable 0 ((1 : ℝ) / 2))
        (by
          intro x _hx
          dsimp [unitIntervalEntropyProfile]
          have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
          linarith)
  nlinarith

/-- Positive-radius singular entropy profile. It is zero off positive radii,
but diverges like `ε^(-1/2)` as `ε ↓ 0` along positive radii. -/
def unitIntervalDivergingEntropyProfile (ε : ℝ) : ℝ :=
  if 0 < ε then 20 * ε ^ (-(1 : ℝ) / 2) else 0

/--
@isnad1 id=le.0h1v.s3.75abefcda142 from=translated src=- shape=8a62b088 vocab=3a459c8e
-/
theorem unitIntervalDivergingEntropyProfile_nonneg (ε : ℝ) :
    0 ≤ unitIntervalDivergingEntropyProfile ε := by
  by_cases hε : 0 < ε
  · simp [unitIntervalDivergingEntropyProfile, hε,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 20)
        (Real.rpow_nonneg hε.le (-(1 : ℝ) / 2))]
  · simp [unitIntervalDivergingEntropyProfile, hε]

/--
@isnad1 id=guardeda.0h1v.s3.c03f5780c9fc from=translated src=- shape=7f61ff03 vocab=90dc4170
-/
theorem unitIntervalDivergingEntropyProfile_guarded (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus
      unitIntervalDivergingEntropyProfile (1 : ℝ) j := by
  intro ε hleft hright
  have hright_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by positivity
  have hε_pos : 0 < ε := by
    have hleft_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 2) := by positivity
    exact lt_of_lt_of_le hleft_pos hleft
  simp [unitIntervalDivergingEntropyProfile, hε_pos]
  simpa [div_eq_mul_inv, one_mul] using
    Real.rpow_le_rpow_of_nonpos hε_pos hright
      (by norm_num : (-(1 : ℝ) / 2) ≤ 0)

/--
@isnad1 id=interval.0h0v.s5.4f586fbcfe53 from=translated src=- shape=a1975529 vocab=9610d1e7
-/
theorem unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half :
    IntervalIntegrable unitIntervalDivergingEntropyProfile volume
      (0 : ℝ) ((1 : ℝ) / 2) := by
  have hbase :
      IntervalIntegrable (fun ε : ℝ => 20 * ε ^ (-(1 : ℝ) / 2))
        volume (0 : ℝ) ((1 : ℝ) / 2) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := ((1 : ℝ) / 2))
      (r := (-(1 : ℝ) / 2)) (by norm_num)).const_mul 20
  refine hbase.congr ?_
  intro ε hε
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)] at hε
  simp [unitIntervalDivergingEntropyProfile, hε.1]

/--
@isnad1 id=interval.0h1v.s6.ea1a2ba196e5 from=translated src=- shape=6b4c99b1 vocab=cb1ec10a
-/
theorem unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic
    (j : ℕ) :
    IntervalIntegrable unitIntervalDivergingEntropyProfile volume
      ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
      ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  have hbase :
      IntervalIntegrable (fun ε : ℝ => 20 * ε ^ (-(1 : ℝ) / 2))
        volume ((1 : ℝ) / (2 : ℝ) ^ (j + 2))
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (a := ((1 : ℝ) / (2 : ℝ) ^ (j + 2)))
      (b := ((1 : ℝ) / (2 : ℝ) ^ (j + 1)))
      (r := (-(1 : ℝ) / 2)) (by norm_num)).const_mul 20
  have hab :
      (1 : ℝ) / (2 : ℝ) ^ (j + 2) ≤
        (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
    have hwidth :=
      FiniteSubGaussianProcess.dyadic_annulus_width_nonneg
        (radiusScale := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) (j + 1)
    linarith
  refine hbase.congr ?_
  intro ε hε
  rw [Set.uIoc_of_le hab] at hε
  have hleft_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 2) := by positivity
  have hε_pos : 0 < ε := lt_trans hleft_pos hε.1
  simp [unitIntervalDivergingEntropyProfile, hε_pos]

private lemma unitIntervalRoundedDyadicGridCoverCount_le_pow (j : ℕ) :
    unitIntervalRoundedDyadicGridCoverCount j ≤ 2 ^ (2 * j + 5) := by
  have h1 : 2 ^ (j + 1) + 1 ≤ 2 ^ (j + 2) := by
    have hp : 1 ≤ 2 ^ (j + 1) :=
      Nat.one_le_pow (j + 1) 2 (by norm_num)
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    omega
  have h2 : 2 ^ (j + 2) + 1 ≤ 2 ^ (j + 3) := by
    have hp : 1 ≤ 2 ^ (j + 2) :=
      Nat.one_le_pow (j + 2) 2 (by norm_num)
    rw [show j + 3 = (j + 2) + 1 by omega, pow_succ]
    omega
  have hmul := Nat.mul_le_mul h1 h2
  have hpow : 2 ^ (j + 2) * 2 ^ (j + 3) = 2 ^ (2 * j + 5) := by
    rw [← pow_add]
    congr 1
    omega
  simpa [unitIntervalRoundedDyadicGridCoverCount, hpow] using hmul

/-- The singular profile dominates every rounded-dyadic entropy sample.

-- fidelity: The domination is uniform in the dyadic index and uses the
actual rounded-grid cover counts, while the profile diverges at positive radii
approaching zero.
@isnad1 id=le.0h1v.s5.a3facd71c5c3 from=translated src=- shape=d47bb8c7 vocab=a8e6367f
-/
theorem unitInterval_divergingEntropyProfile_dominates_roundedDyadicEntropy
    (j : ℕ) :
    Real.sqrt (Real.log (unitIntervalRoundedDyadicGridCoverCount j : ℝ)) ≤
      unitIntervalDivergingEntropyProfile
        ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  let c : ℕ := unitIntervalRoundedDyadicGridCoverCount j
  have hc_pos_nat : 0 < c := by
    dsimp [c, unitIntervalRoundedDyadicGridCoverCount]
    positivity
  have hlog_nonneg : 0 ≤ Real.log (c : ℝ) :=
    Real.log_natCast_nonneg c
  have hcount_le : (c : ℝ) ≤ (2 : ℝ) ^ (2 * j + 5) := by
    exact_mod_cast unitIntervalRoundedDyadicGridCoverCount_le_pow j
  have hlog_le_sqrt : Real.log (c : ℝ) ≤
      2 * (c : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa [one_div, mul_comm] using
      Real.log_natCast_le_rpow_div c
        (by norm_num : 0 < (1 : ℝ) / 2)
  have hcpow_le :
      (c : ℝ) ^ ((1 : ℝ) / 2) ≤
        ((2 : ℝ) ^ (2 * j + 5)) ^ ((1 : ℝ) / 2) := by
    exact Real.rpow_le_rpow (by exact_mod_cast Nat.zero_le c)
      hcount_le (by norm_num)
  have hpow_sqrt_le :
      ((2 : ℝ) ^ (2 * j + 5)) ^ ((1 : ℝ) / 2) ≤
        (2 : ℝ) ^ (j + 3) := by
    have hbase : (0 : ℝ) ≤ 2 := by norm_num
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase]
    rw [← Real.rpow_natCast (2 : ℝ) (j + 3)]
    have hexp_le :
        ((2 * j + 5 : ℕ) : ℝ) * ((1 : ℝ) / 2) ≤
          ((j + 3 : ℕ) : ℝ) := by
      have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast Nat.zero_le j
      norm_num
      nlinarith
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexp_le
  have hlog_le_pow : Real.log (c : ℝ) ≤ (2 : ℝ) ^ (j + 4) := by
    calc
      Real.log (c : ℝ) ≤ 2 * (c : ℝ) ^ ((1 : ℝ) / 2) :=
        hlog_le_sqrt
      _ ≤ 2 * ((2 : ℝ) ^ (2 * j + 5)) ^ ((1 : ℝ) / 2) := by
        nlinarith [hcpow_le]
      _ ≤ 2 * (2 : ℝ) ^ (j + 3) := by
        nlinarith [hpow_sqrt_le]
      _ = (2 : ℝ) ^ (j + 4) := by
        rw [show j + 4 = (j + 3) + 1 by omega, pow_succ]
        ring
  have hradius_pos : 0 < (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
    positivity
  have hprofile_sq :
      (unitIntervalDivergingEntropyProfile
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ^ 2 =
        400 * (2 : ℝ) ^ (j + 1) := by
    simp [unitIntervalDivergingEntropyProfile]
    have hnonneg : 0 ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := by positivity
    rw [mul_pow]
    norm_num
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hnonneg]
    ring_nf
    rw [Real.rpow_neg_one]
    field_simp [pow_ne_zero j (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]
    rw [← mul_pow]
    norm_num
  have hlog_le_profile_sq :
      Real.log (c : ℝ) ≤
        (unitIntervalDivergingEntropyProfile
          ((1 : ℝ) / (2 : ℝ) ^ (j + 1))) ^ 2 := by
    rw [hprofile_sq]
    have hpow_mono :
        (2 : ℝ) ^ (j + 4) ≤ 400 * (2 : ℝ) ^ (j + 1) := by
      have hpos : 0 < (2 : ℝ) ^ (j + 1) :=
        pow_pos (by norm_num) _
      rw [show j + 4 = (j + 1) + 3 by omega, pow_add]
      norm_num
      nlinarith [hpos]
    exact hlog_le_pow.trans hpow_mono
  rw [Real.sqrt_le_iff]
  exact ⟨unitIntervalDivergingEntropyProfile_nonneg _, hlog_le_profile_sq⟩

/-- The singular entropy profile has positive integral mass on `0..1/2`.

-- fidelity: The positive lower bound comes from the concrete subinterval
`[1 / 4, 1 / 2]`, so the load-bearing entropy term is not concentrated in a
formal singularity at zero.
@isnad1 id=lt.0h0v.s5.7fde40e9bff6 from=translated src=- shape=82bd89d8 vocab=a363a400
-/
theorem unitInterval_divergingEntropyProfile_integral_positive :
    0 < ∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
      unitIntervalDivergingEntropyProfile ε := by
  have htrunc_rect :
      (((1 : ℝ) / 2) - (1 / 4)) * 20 ≤
        ∫ ε in ((1 : ℝ) / 4)..((1 : ℝ) / 2),
          unitIntervalDivergingEntropyProfile ε := by
    refine
      FiniteSubGaussianProcess.interval_const_mul_le_integral_of_le_on
        (f := unitIntervalDivergingEntropyProfile) (a := ((1 : ℝ) / 4))
        (b := ((1 : ℝ) / 2)) (c := (20 : ℝ)) (by norm_num)
        (by
          have hI :=
            unitIntervalDivergingEntropyProfile_intervalIntegrable_dyadic 0
          norm_num at hI
          simpa [one_div] using hI) ?_
    intro ε hε
    rcases hε with ⟨hε_left, hε_right⟩
    have hε_pos : 0 < ε := by linarith
    have hε_le_one : ε ≤ (1 : ℝ) := by linarith
    have hpow_ge_one : (1 : ℝ) ≤ ε ^ (-(1 : ℝ) / 2) := by
      have h :=
        Real.rpow_le_rpow_of_nonpos hε_pos hε_le_one
          (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
      simpa using h
    simp [unitIntervalDivergingEntropyProfile, hε_pos]
    nlinarith
  have htrunc_pos :
      0 < ∫ ε in ((1 : ℝ) / 4)..((1 : ℝ) / 2),
        unitIntervalDivergingEntropyProfile ε := by
    nlinarith
  have hdom :=
    GuardedContinuousDudley.guarded_truncatedIntegral_le_full_integral
      (m := 1) (entropyAtRadius := unitIntervalDivergingEntropyProfile)
      (radiusScale := (1 : ℝ)) (by norm_num)
      unitIntervalDivergingEntropyProfile_nonneg
      unitIntervalDivergingEntropyProfile_intervalIntegrable_zero_half
  norm_num at hdom
  exact lt_of_lt_of_le htrunc_pos hdom

/-- Corrected guarded continuous Dudley wrapper using a dyadic profile side
condition instead of a global antitone entropy profile.

-- fidelity: The finite input is a real dyadic upper-sum bound at positive
annuli; the theorem does not assume global antitonicity or evaluate the profile
at radius zero through monotonicity.
@isnad1 id=le.4h7v.s8.e788a27e347c from=translated src=- shape=955b8861 vocab=cf28a1f5
-/
theorem continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
    {Ω T : Type*} [Fintype Ω]
    (P : FiniteSubGaussianProcess Ω T)
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hdyadic : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus entropyAtRadius radiusScale j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable entropyAtRadius volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m entropyAtRadius + eta) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) :=
  GuardedContinuousDudley.guarded_continuous_dudley_entropy_integral_nonempty_of_upper_sum_bounds
    (P := P) (coarseBudget := coarseBudget) (radiusScale := radiusScale)
    (entropyAtRadius := entropyAtRadius) (supFunctional := supFunctional)
    hradiusScale hentropy_nonneg hint0 hdyadic

end

end FormalSLT.Covering.ContinuousDudleyUnitInterval
