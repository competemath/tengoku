import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankAdmissibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Consequences of the fixed-rank diagonal estimate This module packages the exact output shape of Theorem 10.14 and proves its elementary consequences. -/

namespace RankAmplification

open Filter
open scoped Topology

noncomputable section

/-- The error scale in Theorems 1.1 and 10.14.-/
def fixedRankExponentialMajorant
    (J : ℕ) (ε : ℕ → ℝ) (x : ℕ) : ℝ :=
  (x : ℝ) * Real.exp
    (-Real.sqrt J * scaleG (x : ℝ) + ε x * scaleV (x : ℝ))

/--
@isnad1 id=le.0h3v.s4.e7f0a6cdf2d9 from=translated src=- shape=37bc4839 vocab=4790b364
-/
theorem fixedRankExponentialMajorant_nonneg (J : ℕ) (ε : ℕ → ℝ) (x : ℕ) :
    0 ≤ fixedRankExponentialMajorant J ε x := by
  unfold fixedRankExponentialMajorant
  positivity

/-- Exact eventual form of the fixed-rank diagonal decomposition, including its uniform shift range and an explicit multiplicative constant.-/
structure FixedRankDiagonalEstimate
    (J : ℕ) (ε : ℕ → ℝ) (C : ℝ) : Prop where
  rank_pos : 0 < J
  error_tendsto : Tendsto ε atTop (nhds 0)
  constant_nonneg : 0 ≤ C
  bound : ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x →
    (shiftedEqualTotientCount x h : ℝ) ≤
      (aboveCutoffDiagonalCount x h (fixedRankNatUpperY J x) : ℝ) +
        C * fixedRankExponentialMajorant J ε x

/-- Odd shifts remove the displayed diagonal exactly.
@isnad1 id=eventual.1h3v.s6.4c0634fed498 from=translated src=- shape=bfadc7ee vocab=a5aefbf9
-/
theorem FixedRankDiagonalEstimate.odd_bound
    {J : ℕ} {ε : ℕ → ℝ} {C : ℝ}
    (estimate : FixedRankDiagonalEstimate J ε C) :
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x → Odd h →
      (shiftedEqualTotientCount x h : ℝ) ≤
        C * fixedRankExponentialMajorant J ε x := by
  filter_upwards [estimate.bound] with x hx
  intro h hh hhy hodd
  simpa [aboveCutoffDiagonalCount_eq_zero_of_odd hodd] using hx h hh hhy

/-! ## Absorbing a varying `ε(x)V` term -/

/-- A real sequence tending to zero is eventually bounded in absolute value by one.
@isnad1 id=eventual.1h1v.s5.ae5cf47fcec5 from=translated src=- shape=722b8c03 vocab=1d66f6cc
-/
theorem eventually_abs_le_one_of_tendsto_zero
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0)) :
    ∀ᶠ x : ℕ in atTop, |ε x| ≤ 1 := by
  rw [Metric.tendsto_atTop] at hε
  obtain ⟨N, hN⟩ := hε 1 (by norm_num)
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun x hx ↦ hx⟩] with x hx
  have hdist := hN x hx
  simpa [Real.dist_eq] using hdist.le

/-- The varying secondary error is smaller than any fixed positive multiple of `G`.
@isnad1 id=eventual.2h2v.s6.f76bf7c579e2 from=translated src=- shape=d0bcc321 vocab=f8575912
-/
theorem eventually_error_mul_scaleV_le_margin_scaleG
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    {margin : ℝ} (hmargin : 0 < margin) :
    ∀ᶠ x : ℕ in atTop,
      ε x * scaleV (x : ℝ) ≤ margin * scaleG (x : ℝ) := by
  have hVreal : ∀ᶠ x : ℝ in atTop,
      scaleV x ≤ margin * scaleG x := by
    simpa only [one_mul] using
      (eventually_const_mul_scaleV_le_margin_scaleG (c := 1) hmargin)
  have hVnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hVreal
  have hpositive : ∀ᶠ x : ℕ in atTop,
      0 ≤ scaleV (x : ℝ) := by
    have hreal : ∀ᶠ x : ℝ in atTop, 0 ≤ scaleV x := by
      filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
      exact (scaleV_pos hL (scaleG_pos hL hA)).le
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
  filter_upwards [eventually_abs_le_one_of_tendsto_zero hε, hVnat, hpositive] with
      x hεone hV hVnonneg
  calc
    ε x * scaleV (x : ℝ) ≤ |ε x| * scaleV (x : ℝ) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hVnonneg
    _ ≤ 1 * scaleV (x : ℝ) :=
      mul_le_mul_of_nonneg_right hεone hVnonneg
    _ ≤ margin * scaleG (x : ℝ) := by simpa using hV

/-- The fixed-rank exponent with coefficient `√J` eventually dominates every smaller `B`.
@isnad1 id=eventual.2h3v.s6.53488f43d7ae from=translated src=- shape=399826bc vocab=71b4cdf2
-/
theorem eventually_fixedRank_exponent_le_coefficient
    {J : ℕ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    {B : ℝ} (hB : B < Real.sqrt J) :
    ∀ᶠ x : ℕ in atTop,
      -Real.sqrt J * scaleG (x : ℝ) + ε x * scaleV (x : ℝ) ≤
        -B * scaleG (x : ℝ) := by
  have hmargin : 0 < Real.sqrt J - B := sub_pos.mpr hB
  filter_upwards [eventually_error_mul_scaleV_le_margin_scaleG hε hmargin] with x hx
  linarith

/-- Corresponding comparison of exponential majorants.
@isnad1 id=eventual.2h3v.s6.dbef43b12855 from=translated src=- shape=339e7c0f vocab=6ba3d43a
-/
theorem eventually_fixedRankMajorant_le_coefficient
    {J : ℕ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    {B : ℝ} (hB : B < Real.sqrt J) :
    ∀ᶠ x : ℕ in atTop,
      fixedRankExponentialMajorant J ε x ≤
        (x : ℝ) * Real.exp (-B * scaleG (x : ℝ)) := by
  filter_upwards [eventually_fixedRank_exponent_le_coefficient hε hB] with x hx
  unfold fixedRankExponentialMajorant
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (Nat.cast_nonneg x)

/-! ## Corollary 1.2 forms -/

/-- Uniform odd-shift estimate for every coefficient below `√J`.
@isnad1 id=eventual.2h4v.s6.f713a16f549a from=translated src=- shape=8c43d9c3 vocab=0be10875
-/
theorem FixedRankDiagonalEstimate.uniform_odd_coefficient_bound
    {J : ℕ} {ε : ℕ → ℝ} {C B : ℝ}
    (estimate : FixedRankDiagonalEstimate J ε C)
    (hB : B < Real.sqrt J) :
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x → Odd h →
      (shiftedEqualTotientCount x h : ℝ) ≤
        C * ((x : ℝ) * Real.exp (-B * scaleG (x : ℝ))) := by
  filter_upwards [estimate.odd_bound,
    eventually_fixedRankMajorant_le_coefficient estimate.error_tendsto hB] with x hx hmajor
  intro h hh hhy hodd
  exact (hx h hh hhy hodd).trans
    (mul_le_mul_of_nonneg_left hmajor estimate.constant_nonneg)

/-- Every fixed positive shift eventually belongs to the growing fixed-rank shift range.
@isnad1 id=eventual.1h2v.s4.705d9a229c04 from=translated src=- shape=1c44500c vocab=0784f315
-/
theorem eventually_fixed_shift_le_fixedRankNatY
    (J : ℕ) (hJ : 0 < J) (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, h ≤ fixedRankNatY J x :=
  (tendsto_fixedRankNatY_atTop J hJ).eventually_ge_atTop h

/-- Fixed-shift version of Corollary 1.2, with its explicit constant retained.
@isnad1 id=eventual.4h5v.s6.5b13baffed60 from=translated src=- shape=96fde7e0 vocab=23ca41d8
-/
theorem FixedRankDiagonalEstimate.fixed_odd_shift_coefficient_bound
    {J : ℕ} {ε : ℕ → ℝ} {C B : ℝ}
    (estimate : FixedRankDiagonalEstimate J ε C)
    (hB : B < Real.sqrt J) {h : ℕ} (hh : 1 ≤ h) (hodd : Odd h) :
    ∀ᶠ x : ℕ in atTop,
      (shiftedEqualTotientCount x h : ℝ) ≤
        C * ((x : ℝ) * Real.exp (-B * scaleG (x : ℝ))) := by
  have huniform := estimate.uniform_odd_coefficient_bound hB
  filter_upwards [huniform,
    eventually_fixed_shift_le_fixedRankNatY J estimate.rank_pos h] with x hx hhy
  exact hx h hh hhy hodd

end

end RankAmplification
