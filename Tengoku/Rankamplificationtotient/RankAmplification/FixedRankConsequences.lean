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

/-- Odd shifts remove the displayed diagonal exactly.-/
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

/-- A real sequence tending to zero is eventually bounded in absolute value by one.-/
theorem eventually_abs_le_one_of_tendsto_zero
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0)) :
    ∀ᶠ x : ℕ in atTop, |ε x| ≤ 1 := by
  rw [Metric.tendsto_atTop] at hε
  obtain ⟨N, hN⟩ := hε 1 (by norm_num)
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun x hx ↦ hx⟩] with x hx
  have hdist := hN x hx
  simpa [Real.dist_eq] using hdist.le

/-- The varying secondary error is smaller than any fixed positive multiple of `G`.-/
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

/-- The fixed-rank exponent with coefficient `√J` eventually dominates every smaller `B`.-/
theorem eventually_fixedRank_exponent_le_coefficient
    {J : ℕ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    {B : ℝ} (hB : B < Real.sqrt J) :
    ∀ᶠ x : ℕ in atTop,
      -Real.sqrt J * scaleG (x : ℝ) + ε x * scaleV (x : ℝ) ≤
        -B * scaleG (x : ℝ) := by
  have hmargin : 0 < Real.sqrt J - B := sub_pos.mpr hB
  filter_upwards [eventually_error_mul_scaleV_le_margin_scaleG hε hmargin] with x hx
  linarith

/-- Corresponding comparison of exponential majorants.-/
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

/-- Uniform odd-shift estimate for every coefficient below `√J`.-/
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

/-- Every fixed positive shift eventually belongs to the growing fixed-rank shift range.-/
theorem eventually_fixed_shift_le_fixedRankNatY
    (J : ℕ) (hJ : 0 < J) (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, h ≤ fixedRankNatY J x :=
  (tendsto_fixedRankNatY_atTop J hJ).eventually_ge_atTop h

/-- Fixed-shift version of Corollary 1.2, with its explicit constant retained.-/
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
