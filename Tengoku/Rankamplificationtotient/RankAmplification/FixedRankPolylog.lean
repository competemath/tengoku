import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankConsequences
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Polylogarithmic fixed-rank uniformity This module proves that every fixed polylogarithmic shift range is eventually contained in the paper's range `h ≤ exp(G/√J)`. -/

namespace RankAmplification

open Filter Asymptotics
open scoped Topology

noncomputable section

/-! ## Comparing `log₂ x` with `G` -/

/--
@isnad1 id=islittle.0h0v.s3.8f74391cdbf3 from=translated src=- shape=d231363d vocab=f141189c
-/
theorem log2_isLittleO_sqrt_scaleL :
    log2 =o[atTop] (fun x ↦ Real.sqrt (scaleL x)) := by
  have h :=
    (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).comp_tendsto
      tendsto_scaleL_atTop
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    simp [Function.comp_apply, Real.sqrt_eq_rpow]

/--
@isnad1 id=isbigo.0h0v.s3.599d94725e96 from=translated src=- shape=afbd0cda vocab=6847f01b
-/
theorem sqrt_scaleL_isBigO_scaleG :
    (fun x ↦ Real.sqrt (scaleL x)) =O[atTop] scaleG := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_scaleL_pos,
    tendsto_scaleA_atTop.eventually_ge_atTop 1] with x hL hA
  have hprod : scaleL x ≤ scaleL x * scaleA x := by
    nlinarith
  have hsqrt : Real.sqrt (scaleL x) ≤ scaleG x := by
    rw [scaleG_eq]
    exact Real.sqrt_le_sqrt hprod
  have hleft : 0 ≤ Real.sqrt (scaleL x) := Real.sqrt_nonneg _
  have hright : 0 ≤ scaleG x := scaleG_nonneg x
  calc
    ‖Real.sqrt (scaleL x)‖ = Real.sqrt (scaleL x) := Real.norm_of_nonneg hleft
    _ ≤ scaleG x := hsqrt
    _ = ‖scaleG x‖ := (Real.norm_of_nonneg hright).symm
    _ = 1 * ‖scaleG x‖ := by ring

/-- The logarithm of every fixed polylogarithmic range is negligible relative to `G`.
@isnad1 id=islittle.0h0v.s3.bd1abf622b44 from=translated src=- shape=47806ae7 vocab=8f244d9e
-/
theorem log2_isLittleO_scaleG : log2 =o[atTop] scaleG :=
  log2_isLittleO_sqrt_scaleL.trans_isBigO sqrt_scaleL_isBigO_scaleG

/-- For fixed positive `J` and `A₀`, eventually `A₀ log₂ x ≤ T_J`.
@isnad1 id=eventual.2h2v.s5.767cb187475e from=translated src=- shape=9805f73f vocab=2671785a
-/
theorem eventually_mul_log2_le_fixedRankT
    {J : ℕ} (hJ : 0 < J) {A₀ : ℝ} (hA₀ : 0 ≤ A₀) :
    ∀ᶠ x : ℝ in atTop, A₀ * log2 x ≤ fixedRankT J x := by
  by_cases hA₀zero : A₀ = 0
  · subst A₀
    have hT : ∀ᶠ x : ℝ in atTop, 0 ≤ fixedRankT J x :=
      (tendsto_fixedRankT_atTop J hJ).eventually_ge_atTop 0
    simpa using hT
  · have hA₀pos : 0 < A₀ := lt_of_le_of_ne hA₀ (Ne.symm hA₀zero)
    have hsqrtJ : 0 < Real.sqrt J := Real.sqrt_pos.2 (by exact_mod_cast hJ)
    have hc : 0 < (Real.sqrt J)⁻¹ := inv_pos.mpr hsqrtJ
    have hbound := (log2_isLittleO_scaleG.const_mul_left A₀).bound hc
    filter_upwards [hbound, eventually_log2_pos, eventually_scaleL_pos,
      eventually_scaleA_pos] with x hx hlog hL hA
    have hleft : 0 ≤ A₀ * log2 x := mul_nonneg hA₀ hlog.le
    have hG : 0 ≤ scaleG x := (scaleG_pos hL hA).le
    calc
      A₀ * log2 x = ‖A₀ * log2 x‖ := (Real.norm_of_nonneg hleft).symm
      _ ≤ (Real.sqrt J)⁻¹ * ‖scaleG x‖ := by simpa using hx
      _ = fixedRankT J x := by
        rw [Real.norm_of_nonneg hG, fixedRankT, inv_mul_eq_div]

/-! ## Natural polylogarithmic cutoff -/

/-- Natural floor of `(log x)^A₀`.-/
def fixedPolylogCutoff (A₀ : ℝ) (x : ℕ) : ℕ :=
  ⌊(scaleL (x : ℝ)) ^ A₀⌋₊

/--
@isnad1 id=eq.0h2v.s5.5b31bc49bed9 from=translated src=- shape=347b3c1e vocab=3be638e0
-/
@[simp] theorem fixedPolylogCutoff_eq_floor (A₀ : ℝ) (x : ℕ) :
    fixedPolylogCutoff A₀ x = ⌊(scaleL (x : ℝ)) ^ A₀⌋₊ := rfl

/--
@isnad1 id=eventual.2h2v.s5.8813c4c3604f from=translated src=- shape=3e2abef3 vocab=ef706c0d
-/
theorem eventually_polylog_real_le_fixedRankY
    {J : ℕ} (hJ : 0 < J) {A₀ : ℝ} (hA₀ : 0 ≤ A₀) :
    ∀ᶠ x : ℝ in atTop, (scaleL x) ^ A₀ ≤ fixedRankY J x := by
  filter_upwards [eventually_mul_log2_le_fixedRankT hJ hA₀,
    eventually_scaleL_pos] with x hx hL
  rw [Real.rpow_def_of_pos hL, fixedRankY]
  apply Real.exp_le_exp.mpr
  simpa only [log2_eq, scaleL_eq, mul_comm] using hx

/-- Every fixed polylogarithmic natural range lies inside `h ≤ y_J`.
@isnad1 id=eventual.2h2v.s5.c7c9a81a2b1d from=translated src=- shape=cc5e725b vocab=820f435a
-/
theorem eventually_fixedPolylogCutoff_le_fixedRankNatY
    {J : ℕ} (hJ : 0 < J) {A₀ : ℝ} (hA₀ : 0 ≤ A₀) :
    ∀ᶠ x : ℕ in atTop,
      fixedPolylogCutoff A₀ x ≤ fixedRankNatY J x := by
  have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_polylog_real_le_fixedRankY hJ hA₀)
  filter_upwards [hreal] with x hx
  exact Nat.floor_mono hx

/-! ## Corollary 1.3 -/

/-- Polylogarithmically uniform odd-shift consequence at every coefficient `B<√J`.
@isnad1 id=eventual.3h5v.s6.ab0640f20fb1 from=translated src=- shape=fb19855f vocab=39c17b13
-/
theorem FixedRankDiagonalEstimate.polylog_odd_coefficient_bound
    {J : ℕ} {ε : ℕ → ℝ} {C B A₀ : ℝ}
    (estimate : FixedRankDiagonalEstimate J ε C)
    (hB : B < Real.sqrt J) (hA₀ : 0 ≤ A₀) :
    ∀ᶠ x : ℕ in atTop, ∀ h, 1 ≤ h → h ≤ fixedPolylogCutoff A₀ x → Odd h →
      (shiftedEqualTotientCount x h : ℝ) ≤
        C * ((x : ℝ) * Real.exp (-B * scaleG (x : ℝ))) := by
  have huniform := estimate.uniform_odd_coefficient_bound hB
  filter_upwards [huniform,
    eventually_fixedPolylogCutoff_le_fixedRankNatY estimate.rank_pos hA₀] with
      x hx hpoly
  intro h hh hhrange hodd
  exact hx h hh (hhrange.trans hpoly) hodd

end

end RankAmplification
