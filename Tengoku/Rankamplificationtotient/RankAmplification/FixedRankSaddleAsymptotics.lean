import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankScales
import Tengoku.Rankamplificationtotient.RankAmplification.MovingScales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed-rank smooth saddle asymptotics For a logarithmic cutoff `T`, the smooth-number rate used in the fixed-rank argument is `Sₓ(T) = (L/T) (log₂(L/T) + log₃(L/T))`. -/

namespace RankAmplification

open Filter Asymptotics
open scoped Topology Asymptotics

noncomputable section

/-! ## Definitions and exact saddle algebra -/

/-- The paper's fixed-rank smooth rate `Sₓ(T)`.-/
def fixedRankSmoothRate (x T : ℝ) : ℝ :=
  (scaleL x / T) *
    (log2 (scaleL x / T) + log3 (scaleL x / T))

/-- The smooth rate evaluated at `T_J = G/√J`.-/
def fixedRankSaddleRate (J : ℕ) (x : ℝ) : ℝ :=
  fixedRankSmoothRate x (fixedRankT J x)

/-- Error after removing the main exponent `√J G`.-/
def fixedRankSaddleError (J : ℕ) (x : ℝ) : ℝ :=
  fixedRankSaddleRate J x - Real.sqrt J * scaleG x

/-- The explicit `V`-normalized fixed-rank saddle error.-/
def fixedRankSaddleNormalizedError (J : ℕ) (x : ℝ) : ℝ :=
  fixedRankSaddleError J x / scaleV x

/-- The saddle Rankin parameter is exactly `√J V`.-/
theorem scaleL_div_fixedRankT_eq_sqrt_mul_scaleV
    {J : ℕ} {x : ℝ} (hJ : 0 < J) (hG : scaleG x ≠ 0) :
    scaleL x / fixedRankT J x = Real.sqrt J * scaleV x := by
  have hsqrt : Real.sqrt (J : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hJ)).ne'
  rw [fixedRankT, scaleV_eq]
  field_simp [hsqrt, hG]

/-- Exact unfolded rate at the saddle.-/
theorem fixedRankSaddleRate_eq
    {J : ℕ} {x : ℝ} (hJ : 0 < J) (hG : scaleG x ≠ 0) :
    fixedRankSaddleRate J x =
      (Real.sqrt J * scaleV x) *
        (log2 (Real.sqrt J * scaleV x) +
          log3 (Real.sqrt J * scaleV x)) := by
  rw [fixedRankSaddleRate, fixedRankSmoothRate,
    scaleL_div_fixedRankT_eq_sqrt_mul_scaleV hJ hG]

/-- Requested exact cutoff hookup: `J T_J = √J G`.-/
theorem fixedRank_J_mul_T_eq_sqrt_mul_G
    {J : ℕ} {x : ℝ} (hJ : 0 < J) :
    (J : ℝ) * fixedRankT J x = Real.sqrt J * scaleG x :=
  nat_mul_fixedRankT hJ

/-- On the positive scale range, `V²=L/A`.-/
theorem scaleV_sq_eq_scaleL_div_scaleA
    {x : ℝ} (hL : 0 < scaleL x) (hA : 0 < scaleA x) :
    scaleV x ^ 2 = scaleL x / scaleA x := by
  have hG := scaleG_pos hL hA
  have hGsq := scaleG_sq hL.le hA.le
  rw [scaleV_eq]
  field_simp [hG.ne', hA.ne']
  nlinarith

/-- Exact logarithmic form `2 log V = L₂ - log A`.-/
theorem two_mul_log_scaleV
    {x : ℝ} (hL : 0 < scaleL x) (hA : 0 < scaleA x) :
    2 * Real.log (scaleV x) = log2 x - Real.log (scaleA x) := by
  have hV := scaleV_pos hL (scaleG_pos hL hA)
  calc
    2 * Real.log (scaleV x) = Real.log (scaleV x ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ = Real.log (scaleL x / scaleA x) := by
      rw [scaleV_sq_eq_scaleL_div_scaleA hL hA]
    _ = Real.log (scaleL x) - Real.log (scaleA x) := by
      rw [Real.log_div hL.ne' hA.ne']
    _ = log2 x - Real.log (scaleA x) := by
      simp only [log2_eq, scaleL_eq]

/-- Exact normalized error formula.-/
theorem fixedRankSaddleNormalizedError_eq
    {J : ℕ} {x : ℝ} (hJ : 0 < J)
    (hL : 0 < scaleL x) (hA : 0 < scaleA x) :
    fixedRankSaddleNormalizedError J x =
      Real.sqrt J *
        (log2 (Real.sqrt J * scaleV x) +
          log3 (Real.sqrt J * scaleV x) - scaleA x) := by
  have hG := scaleG_pos hL hA
  have hV := scaleV_pos hL hG
  have hAG : scaleA x * scaleV x = scaleG x :=
    scaleA_mul_scaleV hL.le hA.le hG.ne'
  rw [fixedRankSaddleNormalizedError, fixedRankSaddleError,
    fixedRankSaddleRate_eq hJ hG.ne']
  field_simp [hV.ne']
  nlinarith

/-! ## The first logarithmic normalization -/

/-- The logarithm of `A` is negligible compared with `L₂`.-/
theorem log_scaleA_isLittleO_log2 :
    (fun x ↦ Real.log (scaleA x)) =o[atTop] log2 := by
  have hlogA : (fun x ↦ Real.log (scaleA x)) =o[atTop] scaleA := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_scaleA_atTop
    apply h.congr'
    · filter_upwards [] with x
      rfl
    · filter_upwards [] with x
      rfl
  exact hlogA.trans scaleA_isLittleO_log2

/-- The inner logarithm of `√J V` is asymptotic to `L₂/2`.-/
theorem tendsto_log_sqrt_mul_scaleV_div_half_log2_one
    (J : ℕ) (hJ : 0 < J) :
    Tendsto
      (fun x ↦ Real.log (Real.sqrt J * scaleV x) /
        ((1 / 2 : ℝ) * log2 x))
      atTop (nhds 1) := by
  have hc : Tendsto
      (fun x ↦ (2 * Real.log (Real.sqrt J)) / log2 x)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log2_atTop
  have hA : Tendsto
      (fun x ↦ Real.log (scaleA x) / log2 x)
      atTop (nhds 0) :=
    log_scaleA_isLittleO_log2.tendsto_div_nhds_zero
  have hmodel : Tendsto
      (fun x ↦ (1 : ℝ) +
        (2 * Real.log (Real.sqrt J)) / log2 x -
          Real.log (scaleA x) / log2 x)
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hraw : Tendsto
        (fun x ↦ (1 : ℝ) +
          ((2 * Real.log (Real.sqrt J)) / log2 x -
            Real.log (scaleA x) / log2 x))
        atTop (nhds 1) := by
      simpa only [sub_self, add_zero] using hone.add (hc.sub hA)
    apply hraw.congr'
    filter_upwards [] with x
    ring
  apply hmodel.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos,
      eventually_log2_pos] with x hL hApos hL2
  have hsqrtJ : 0 < Real.sqrt (J : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hJ)
  have hV : 0 < scaleV x := scaleV_pos hL (scaleG_pos hL hApos)
  rw [Real.log_mul hsqrtJ.ne' hV.ne']
  have hlogV := two_mul_log_scaleV hL hApos
  field_simp [hL2.ne']
  nlinarith

/-! ## The two iterated-logarithm errors -/

/-- First expansion: `log₂(√J V) = log₃ x - log 2 + o(1)`.-/
theorem tendsto_fixedRank_log2_error_zero
    (J : ℕ) (hJ : 0 < J) :
    Tendsto
      (fun x ↦ log2 (Real.sqrt J * scaleV x) - log3 x + Real.log 2)
      atTop (nhds 0) := by
  have hratio := tendsto_log_sqrt_mul_scaleV_div_half_log2_one J hJ
  have hlogRatio : Tendsto
      (fun x ↦ Real.log
        (Real.log (Real.sqrt J * scaleV x) / ((1 / 2 : ℝ) * log2 x)))
      atTop (nhds 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    change Tendsto
      (Real.log ∘ (fun x ↦ Real.log (Real.sqrt J * scaleV x) /
        ((1 / 2 : ℝ) * log2 x))) atTop (nhds 0)
    simpa only [Real.log_one] using hcont
  apply hlogRatio.congr'
  have hsqrtJ : 0 < Real.sqrt (J : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hJ)
  have hinner : Tendsto
      (fun x ↦ Real.log (Real.sqrt J * scaleV x)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_scaleV_atTop.const_mul_atTop hsqrtJ)
  filter_upwards [hinner.eventually_gt_atTop 0, eventually_log2_pos] with x hinnerPos hL2
  have hhalf : 0 < (1 / 2 : ℝ) * log2 x := mul_pos (by norm_num) hL2
  rw [Real.log_div hinnerPos.ne' hhalf.ne', Real.log_mul (by norm_num) hL2.ne']
  simp only [log2_eq, log3_eq]
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one]
    ring
  rw [hlogHalf]
  ring

/-- The first iterated logarithm at the saddle itself tends to infinity.-/
theorem tendsto_log2_sqrt_mul_scaleV_atTop
    (J : ℕ) (hJ : 0 < J) :
    Tendsto (fun x ↦ log2 (Real.sqrt J * scaleV x)) atTop atTop := by
  have hsqrtJ : 0 < Real.sqrt (J : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hJ)
  change Tendsto
    (fun x ↦ Real.log (Real.log (Real.sqrt J * scaleV x))) atTop atTop
  exact Real.tendsto_log_atTop.comp <|
    Real.tendsto_log_atTop.comp
      (tendsto_scaleV_atTop.const_mul_atTop hsqrtJ)

/-- Second expansion: `log₃(√J V) = log₄ x + o(1)`.-/
theorem tendsto_fixedRank_log3_error_zero
    (J : ℕ) (hJ : 0 < J) :
    Tendsto
      (fun x ↦ log3 (Real.sqrt J * scaleV x) - log4 x)
      atTop (nhds 0) := by
  have hsecond := tendsto_fixedRank_log2_error_zero J hJ
  have hdiff : Tendsto
      (fun x ↦ log2 (Real.sqrt J * scaleV x) - log3 x)
      atTop (nhds (-Real.log 2)) := by
    have h := hsecond.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ ↦ Real.log 2) atTop (nhds (Real.log 2)))
    have hraw : Tendsto
        (fun x ↦
          (log2 (Real.sqrt J * scaleV x) - log3 x + Real.log 2) - Real.log 2)
        atTop (nhds (-Real.log 2)) := by
      simpa only [zero_sub] using h
    apply hraw.congr'
    filter_upwards [] with x
    ring
  have hsmall : Tendsto
      (fun x ↦
        (log2 (Real.sqrt J * scaleV x) - log3 x) / log3 x)
      atTop (nhds 0) :=
    hdiff.div_atTop tendsto_log3_atTop
  have hratio : Tendsto
      (fun x ↦ log2 (Real.sqrt J * scaleV x) / log3 x)
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hmodel := hone.add hsmall
    have hmodel' : Tendsto
        (fun x ↦ (1 : ℝ) +
          (log2 (Real.sqrt J * scaleV x) - log3 x) / log3 x)
        atTop (nhds 1) := by
      simpa only [add_zero] using hmodel
    apply hmodel'.congr'
    filter_upwards [eventually_log3_pos] with x hL3
    field_simp [hL3.ne']
    ring
  have hlogRatio : Tendsto
      (fun x ↦ Real.log
        (log2 (Real.sqrt J * scaleV x) / log3 x))
      atTop (nhds 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    change Tendsto
      (Real.log ∘ (fun x ↦ log2 (Real.sqrt J * scaleV x) / log3 x))
      atTop (nhds 0)
    simpa only [Real.log_one] using hcont
  apply hlogRatio.congr'
  filter_upwards [
      (tendsto_log2_sqrt_mul_scaleV_atTop J hJ).eventually_gt_atTop 0,
      eventually_log3_pos] with x hleft hright
  rw [Real.log_div hleft.ne' hright.ne']
  rfl

/-- The full logarithmic bracket in the fixed-rank saddle differs from `A` by `o(1)`.-/
theorem tendsto_fixedRank_saddleBracket_sub_scaleA_zero
    (J : ℕ) (hJ : 0 < J) :
    Tendsto
      (fun x ↦ log2 (Real.sqrt J * scaleV x) +
        log3 (Real.sqrt J * scaleV x) - scaleA x)
      atTop (nhds 0) := by
  have h2 := tendsto_fixedRank_log2_error_zero J hJ
  have h3 := tendsto_fixedRank_log3_error_zero J hJ
  have hsum := h2.add h3
  have hsum' : Tendsto
      (fun x ↦ (log2 (Real.sqrt J * scaleV x) - log3 x + Real.log 2) +
        (log3 (Real.sqrt J * scaleV x) - log4 x))
      atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  apply hsum'.congr'
  filter_upwards [] with x
  simp only [scaleA_eq]
  ring

/-! ## The `o_J(V)` conclusion -/

/-- Explicit normalized form of the paper's fixed-rank saddle asymptotic.-/
theorem tendsto_fixedRankSaddleNormalizedError_zero
    (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankSaddleNormalizedError J) atTop (nhds 0) := by
  have hbracket := tendsto_fixedRank_saddleBracket_sub_scaleA_zero J hJ
  have hscaled : Tendsto
      (fun x ↦ Real.sqrt J *
        (log2 (Real.sqrt J * scaleV x) +
          log3 (Real.sqrt J * scaleV x) - scaleA x))
      atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℝ ↦ Real.sqrt J) atTop (nhds (Real.sqrt J)) :=
      tendsto_const_nhds
    have hmul := hc.mul hbracket
    simpa only [mul_zero] using hmul
  apply hscaled.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  exact (fixedRankSaddleNormalizedError_eq hJ hL hA).symm

/-- Main theorem: at `T=G/√J`, the smooth rate is `√J G + o_J(V)`.-/
theorem fixedRankSaddleError_isLittleO_scaleV
    (J : ℕ) (hJ : 0 < J) :
    (fun x ↦ fixedRankSaddleRate J x - Real.sqrt J * scaleG x)
      =o[atTop] scaleV := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
    intro hzero
    have hV : 0 < scaleV x := scaleV_pos hL (scaleG_pos hL hA)
    exact (hV.ne' hzero).elim
  · change Tendsto (fixedRankSaddleNormalizedError J) atTop (nhds 0)
    exact tendsto_fixedRankSaddleNormalizedError_zero J hJ

/-- Equivalent named form with the smooth-rate definition exposed.-/
theorem fixedRankSmoothRate_at_saddle_isLittleO
    (J : ℕ) (hJ : 0 < J) :
    (fun x ↦ fixedRankSmoothRate x (scaleG x / Real.sqrt J) -
      Real.sqrt J * scaleG x) =o[atTop] scaleV := by
  simpa only [fixedRankSaddleRate, fixedRankT] using
    fixedRankSaddleError_isLittleO_scaleV J hJ

/-- Quantified consequence: every positive multiple of `V` eventually bounds the absolute fixed-rank saddle error.-/
theorem eventually_fixedRankSaddleError_norm_le
    (J : ℕ) (hJ : 0 < J) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      ‖fixedRankSaddleRate J x - Real.sqrt J * scaleG x‖ ≤
        c * ‖scaleV x‖ :=
  (fixedRankSaddleError_isLittleO_scaleV J hJ).bound hc

end

end RankAmplification
