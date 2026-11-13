import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankConsequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed-rank analytic assembly This module connects the exact four-branch decomposition for Theorem 10.14 to its three analytic estimates. -/

namespace RankAmplification

open Filter
open scoped Topology

noncomputable section

/-! ## The three analytic endpoints -/

/-- The fixed-rank form of Lemma 10.6 at the paper's natural cutoffs.-/
def FixedRankLowRankHypothesis (J : ℕ) (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x →
      (paperFixedLowRankShiftedCount J x h : ℝ) ≤
        fixedRankExponentialMajorant J ε x

/-- The fixed-rank form of Proposition 10.12 after supplier coverage and convolution.-/
def FixedRankHighRankHypothesis (J : ℕ) (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x →
      (paperFixedHighRankShiftedCount J x h : ℝ) ≤
        fixedRankExponentialMajorant J ε x

/-- The fixed-rank Proposition 5.1/Proposition 9.7 transfer above the upper cutoff.-/
def FixedRankOffDiagonalHypothesis (J : ℕ) (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x →
      (offDiagonalNonsmoothCount x h (fixedRankNatUpperY J x) : ℝ) ≤
        fixedRankExponentialMajorant J ε x

/-- The exact analytic inputs still required by the fixed-rank proof.-/
structure FixedRankAnalyticData
    (J : ℕ) (εlow εhigh εoff : ℕ → ℝ) : Prop where
  rank_pos : 0 < J
  lowRank : FixedRankLowRankHypothesis J εlow
  highRank : FixedRankHighRankHypothesis J εhigh
  offDiagonal : FixedRankOffDiagonalHypothesis J εoff

/-! ## Combining three vanishing errors -/

/-- Pointwise maximum of the three branchwise normalized errors.-/
def fixedRankMaximumError
    (εlow εhigh εoff : ℕ → ℝ) (x : ℕ) : ℝ :=
  max (max (εlow x) (εhigh x)) (εoff x)

/-- The harmless normalization which absorbs three copies of the branch majorant.-/
def fixedRankCombinedError
    (εlow εhigh εoff : ℕ → ℝ) (x : ℕ) : ℝ :=
  fixedRankMaximumError εlow εhigh εoff x +
    Real.log 3 / scaleV (x : ℝ)

theorem tendsto_scaleV_nat_atTop :
    Tendsto (fun x : ℕ ↦ scaleV (x : ℝ)) atTop atTop :=
  tendsto_scaleV_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem eventually_scaleV_nat_pos :
    ∀ᶠ x : ℕ in atTop, 0 < scaleV (x : ℝ) :=
  tendsto_scaleV_nat_atTop.eventually_gt_atTop 0

theorem tendsto_fixedRankMaximumError_zero
    {εlow εhigh εoff : ℕ → ℝ}
    (hlow : Tendsto εlow atTop (nhds 0))
    (hhigh : Tendsto εhigh atTop (nhds 0))
    (hoff : Tendsto εoff atTop (nhds 0)) :
    Tendsto (fixedRankMaximumError εlow εhigh εoff) atTop (nhds 0) := by
  change Tendsto (fun x ↦ max (max (εlow x) (εhigh x)) (εoff x)) atTop (nhds 0)
  simpa only [max_self] using (hlow.max hhigh).max hoff

theorem tendsto_fixedRankCombinedError_zero
    {εlow εhigh εoff : ℕ → ℝ}
    (hlow : Tendsto εlow atTop (nhds 0))
    (hhigh : Tendsto εhigh atTop (nhds 0))
    (hoff : Tendsto εoff atTop (nhds 0)) :
    Tendsto (fixedRankCombinedError εlow εhigh εoff) atTop (nhds 0) := by
  have hmax := tendsto_fixedRankMaximumError_zero hlow hhigh hoff
  have hquot : Tendsto (fun x : ℕ ↦ Real.log 3 / scaleV (x : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_scaleV_nat_atTop
  change Tendsto (fun x ↦ fixedRankMaximumError εlow εhigh εoff x +
    Real.log 3 / scaleV (x : ℝ)) atTop (nhds 0)
  simpa only [zero_add] using hmax.add hquot

/-! ## Three exponential branch bounds become one -/

theorem sum_three_fixedRankExponentialMajorant_le_combined
    {J x : ℕ} {εlow εhigh εoff : ℕ → ℝ}
    (hV : 0 < scaleV (x : ℝ)) :
    fixedRankExponentialMajorant J εoff x +
        fixedRankExponentialMajorant J εlow x +
        fixedRankExponentialMajorant J εhigh x ≤
      fixedRankExponentialMajorant J
        (fixedRankCombinedError εlow εhigh εoff) x := by
  let M := fixedRankMaximumError εlow εhigh εoff x
  have hlowM : εlow x ≤ M := le_max_of_le_left (le_max_left _ _)
  have hhighM : εhigh x ≤ M := le_max_of_le_left (le_max_right _ _)
  have hoffM : εoff x ≤ M := le_max_right _ _
  have hmono (ε : ℝ) (hε : ε ≤ M) :
      (x : ℝ) * Real.exp
          (-Real.sqrt J * scaleG (x : ℝ) + ε * scaleV (x : ℝ)) ≤
        (x : ℝ) * Real.exp
          (-Real.sqrt J * scaleG (x : ℝ) + M * scaleV (x : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right hε hV.le]
  have hsum :
      fixedRankExponentialMajorant J εoff x +
          fixedRankExponentialMajorant J εlow x +
          fixedRankExponentialMajorant J εhigh x ≤
        3 * ((x : ℝ) * Real.exp
          (-Real.sqrt J * scaleG (x : ℝ) + M * scaleV (x : ℝ))) := by
    unfold fixedRankExponentialMajorant
    linarith [hmono _ hoffM, hmono _ hlowM, hmono _ hhighM]
  calc
    fixedRankExponentialMajorant J εoff x +
        fixedRankExponentialMajorant J εlow x +
        fixedRankExponentialMajorant J εhigh x ≤
      3 * ((x : ℝ) * Real.exp
        (-Real.sqrt J * scaleG (x : ℝ) + M * scaleV (x : ℝ))) := hsum
    _ = fixedRankExponentialMajorant J
        (fixedRankCombinedError εlow εhigh εoff) x := by
      unfold fixedRankExponentialMajorant fixedRankCombinedError
      change 3 * ((x : ℝ) * Real.exp
          (-Real.sqrt J * scaleG (x : ℝ) + M * scaleV (x : ℝ))) =
        (x : ℝ) * Real.exp
          (-Real.sqrt J * scaleG (x : ℝ) +
            (M + Real.log 3 / scaleV (x : ℝ)) * scaleV (x : ℝ))
      have hcancel : Real.log 3 / scaleV (x : ℝ) * scaleV (x : ℝ) =
          Real.log 3 := div_mul_cancel₀ _ hV.ne'
      rw [add_mul, hcancel]
      conv_rhs =>
        rw [← add_assoc, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      ring

/-! ## Theorems 10.13 and 10.14 at the optimized cutoff -/

/-- The exact fixed-rank diagonal estimate assembled from the three analytic branches.-/
theorem fixedRankDiagonalEstimate_of_analyticData
    {J : ℕ} {εlow εhigh εoff : ℕ → ℝ}
    (data : FixedRankAnalyticData J εlow εhigh εoff) :
    FixedRankDiagonalEstimate J
      (fixedRankCombinedError εlow εhigh εoff) 1 := by
  refine ⟨data.rank_pos,
    tendsto_fixedRankCombinedError_zero data.lowRank.1
      data.highRank.1 data.offDiagonal.1,
    by norm_num, ?_⟩
  filter_upwards [data.lowRank.2, data.highRank.2, data.offDiagonal.2,
    eventually_scaleV_nat_pos] with x hlow hhigh hoff hV
  intro h hh hhy
  have hdecomp := fixedRank_count_le_diagonal_add_branches
    (FixedRankBranchBounds.mk (hlow h hh hhy) (hhigh h hh hhy) (hoff h hh hhy))
  have hsum := sum_three_fixedRankExponentialMajorant_le_combined
    (J := J) (x := x) (εlow := εlow) (εhigh := εhigh) (εoff := εoff) hV
  calc
    (shiftedEqualTotientCount x h : ℝ) ≤
        (aboveCutoffDiagonalCount x h (fixedRankNatUpperY J x) : ℝ) +
          fixedRankExponentialMajorant J εoff x +
          fixedRankExponentialMajorant J εlow x +
          fixedRankExponentialMajorant J εhigh x := hdecomp
    _ ≤ (aboveCutoffDiagonalCount x h (fixedRankNatUpperY J x) : ℝ) +
        fixedRankExponentialMajorant J
          (fixedRankCombinedError εlow εhigh εoff) x := by
      linarith
    _ = (aboveCutoffDiagonalCount x h (fixedRankNatUpperY J x) : ℝ) +
        1 * fixedRankExponentialMajorant J
          (fixedRankCombinedError εlow εhigh εoff) x := by ring

/-- The optimized form of Theorem 10.14, with all analytic dependencies explicit.-/
theorem fixedRank_theorem10_14
    {J : ℕ} {εlow εhigh εoff : ℕ → ℝ}
    (data : FixedRankAnalyticData J εlow εhigh εoff) :
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x →
      (shiftedEqualTotientCount x h : ℝ) ≤
        (aboveCutoffDiagonalCount x h (fixedRankNatUpperY J x) : ℝ) +
          fixedRankExponentialMajorant J
            (fixedRankCombinedError εlow εhigh εoff) x := by
  simpa using (fixedRankDiagonalEstimate_of_analyticData data).bound

/-- Odd shifts remove the diagonal from the assembled fixed-rank theorem.-/
theorem fixedRank_odd_shift_bound_of_analyticData
    {J : ℕ} {εlow εhigh εoff : ℕ → ℝ}
    (data : FixedRankAnalyticData J εlow εhigh εoff) :
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedRankNatY J x → Odd h →
      (shiftedEqualTotientCount x h : ℝ) ≤
        fixedRankExponentialMajorant J
          (fixedRankCombinedError εlow εhigh εoff) x := by
  simpa using (fixedRankDiagonalEstimate_of_analyticData data).odd_bound

end

end RankAmplification
