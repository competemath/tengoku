import Tengoku.Seed.Analysis.Asymptotics.AsymptoticEquivalent
import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Analysis.SpecialFunctions.Log.InvLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed-rank logarithmic scales This module defines the real-valued scales used in the fixed-rank argument. -/

namespace RankAmplification

open Filter
open scoped Asymptotics Topology

noncomputable section

/-- The `n`-fold real logarithm, totalized using Mathlib's total real logarithm.-/
def iteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.log (iteratedLog n x)

/-- The second iterated logarithm.-/
def log2 (x : ℝ) : ℝ := iteratedLog 2 x

/-- The third iterated logarithm.-/
def log3 (x : ℝ) : ℝ := iteratedLog 3 x

/-- The fourth iterated logarithm.-/
def log4 (x : ℝ) : ℝ := iteratedLog 4 x

/-- The paper's scale `L = log x`.-/
def scaleL (x : ℝ) : ℝ := Real.log x

/-- The paper's scale `A = log₃ x + log₄ x - log 2`.-/
def scaleA (x : ℝ) : ℝ := log3 x + log4 x - Real.log 2

/-- The paper's scale `G = √(LA)`, using the total real square root.-/
def scaleG (x : ℝ) : ℝ := Real.sqrt (scaleL x * scaleA x)

/-- The paper's scale `V = L/G`, using total division.-/
def scaleV (x : ℝ) : ℝ := scaleL x / scaleG x

@[simp]
theorem iteratedLog_zero (x : ℝ) : iteratedLog 0 x = x := rfl

@[simp]
theorem iteratedLog_succ (n : ℕ) (x : ℝ) :
    iteratedLog (n + 1) x = Real.log (iteratedLog n x) := rfl

@[simp]
theorem iteratedLog_one (x : ℝ) : iteratedLog 1 x = Real.log x := rfl

@[simp]
theorem log2_eq (x : ℝ) : log2 x = Real.log (Real.log x) := rfl

@[simp]
theorem log3_eq (x : ℝ) : log3 x = Real.log (log2 x) := rfl

@[simp]
theorem log4_eq (x : ℝ) : log4 x = Real.log (log3 x) := rfl

@[simp]
theorem scaleL_eq (x : ℝ) : scaleL x = Real.log x := rfl

@[simp]
theorem scaleA_eq (x : ℝ) : scaleA x = log3 x + log4 x - Real.log 2 := rfl

@[simp]
theorem scaleG_eq (x : ℝ) : scaleG x = Real.sqrt (scaleL x * scaleA x) := rfl

@[simp]
theorem scaleV_eq (x : ℝ) : scaleV x = scaleL x / scaleG x := rfl

/-- Every fixed iterate of the logarithm tends to infinity.-/
theorem tendsto_iteratedLog_atTop (n : ℕ) : Tendsto (iteratedLog n) atTop atTop := by
  induction n with
  | zero => exact tendsto_id
  | succ n ih =>
      change Tendsto (fun x => Real.log (iteratedLog n x)) atTop atTop
      exact Real.tendsto_log_atTop.comp ih

theorem tendsto_log2_atTop : Tendsto log2 atTop atTop := by
  change Tendsto (iteratedLog 2) atTop atTop
  exact tendsto_iteratedLog_atTop 2

theorem tendsto_log3_atTop : Tendsto log3 atTop atTop := by
  change Tendsto (iteratedLog 3) atTop atTop
  exact tendsto_iteratedLog_atTop 3

theorem tendsto_log4_atTop : Tendsto log4 atTop atTop := by
  change Tendsto (iteratedLog 4) atTop atTop
  exact tendsto_iteratedLog_atTop 4

theorem tendsto_scaleL_atTop : Tendsto scaleL atTop atTop := by
  change Tendsto Real.log atTop atTop
  exact Real.tendsto_log_atTop

/-- Each iterated logarithm is eventually positive.-/
theorem eventually_iteratedLog_pos (n : ℕ) : ∀ᶠ x in atTop, 0 < iteratedLog n x :=
  (tendsto_iteratedLog_atTop n).eventually_gt_atTop 0

theorem eventually_log2_pos : ∀ᶠ x in atTop, 0 < log2 x :=
  tendsto_log2_atTop.eventually_gt_atTop 0

theorem eventually_log3_pos : ∀ᶠ x in atTop, 0 < log3 x :=
  tendsto_log3_atTop.eventually_gt_atTop 0

theorem eventually_log4_pos : ∀ᶠ x in atTop, 0 < log4 x :=
  tendsto_log4_atTop.eventually_gt_atTop 0

theorem scaleL_pos {x : ℝ} (hx : 1 < x) : 0 < scaleL x :=
  Real.log_pos hx

theorem log2_pos {x : ℝ} (hx : 1 < Real.log x) : 0 < log2 x := by
  rw [log2_eq]
  exact Real.log_pos hx

theorem log3_pos {x : ℝ} (hx : 1 < log2 x) : 0 < log3 x := by
  rw [log3_eq]
  exact Real.log_pos hx

theorem log4_pos {x : ℝ} (hx : 1 < log3 x) : 0 < log4 x := by
  rw [log4_eq]
  exact Real.log_pos hx

theorem scaleA_pos {x : ℝ} (hx : Real.log 2 < log3 x + log4 x) : 0 < scaleA x := by
  simpa only [scaleA_eq, sub_pos] using hx

theorem scaleA_nonneg {x : ℝ} (hx : Real.log 2 ≤ log3 x + log4 x) : 0 ≤ scaleA x := by
  simpa only [scaleA_eq, sub_nonneg] using hx

theorem scaleG_nonneg (x : ℝ) : 0 ≤ scaleG x :=
  Real.sqrt_nonneg _

theorem scaleG_pos {x : ℝ} (hL : 0 < scaleL x) (hA : 0 < scaleA x) : 0 < scaleG x := by
  rw [scaleG_eq, Real.sqrt_pos]
  exact mul_pos hL hA

theorem scaleV_pos {x : ℝ} (hL : 0 < scaleL x) (hG : 0 < scaleG x) : 0 < scaleV x := by
  rw [scaleV_eq]
  exact div_pos hL hG

/-- Squaring `G` recovers `L A` in the nonnegative range.-/
theorem scaleG_sq {x : ℝ} (hL : 0 ≤ scaleL x) (hA : 0 ≤ scaleA x) :
    scaleG x ^ 2 = scaleL x * scaleA x := by
  rw [scaleG_eq, Real.sq_sqrt (mul_nonneg hL hA)]

/-- The defining cancellation `G V = L`.-/
theorem scaleG_mul_scaleV {x : ℝ} (hG : scaleG x ≠ 0) :
    scaleG x * scaleV x = scaleL x := by
  rw [scaleV_eq]
  exact mul_div_cancel₀ _ hG

theorem scaleV_mul_scaleG {x : ℝ} (hG : scaleG x ≠ 0) :
    scaleV x * scaleG x = scaleL x := by
  rw [mul_comm]
  exact scaleG_mul_scaleV hG

/-- In the positive range, `A V = G`.-/
theorem scaleA_mul_scaleV {x : ℝ} (hL : 0 ≤ scaleL x) (hA : 0 ≤ scaleA x)
    (hG : scaleG x ≠ 0) : scaleA x * scaleV x = scaleG x := by
  rw [scaleV_eq]
  have hsq := scaleG_sq hL hA
  field_simp
  nlinarith

/-- In the positive range, `G / V = A`.-/
theorem scaleG_div_scaleV {x : ℝ} (hL : 0 < scaleL x) (hA : 0 ≤ scaleA x)
    (hG : scaleG x ≠ 0) : scaleG x / scaleV x = scaleA x := by
  rw [scaleV_eq]
  have hsq := scaleG_sq hL.le hA
  have hG' : 0 ≠ scaleG x := hG.symm
  field_simp [hG', ne_of_gt hL]
  nlinarith

/-- The quotient `G/L` is the square root of `A/L` in the positive range.-/
theorem scaleG_div_scaleL_eq_sqrt_div {x : ℝ} (hL : 0 < scaleL x)
    (hA : 0 ≤ scaleA x) :
    scaleG x / scaleL x = Real.sqrt (scaleA x / scaleL x) := by
  calc
    scaleG x / scaleL x =
        (Real.sqrt (scaleL x) * Real.sqrt (scaleA x)) / scaleL x := by
          rw [scaleG_eq, Real.sqrt_mul hL.le]
    _ = Real.sqrt (scaleA x) / Real.sqrt (scaleL x) := by
      have hden : scaleL x = Real.sqrt (scaleL x) * Real.sqrt (scaleL x) :=
        (Real.mul_self_sqrt hL.le).symm
      calc
        (Real.sqrt (scaleL x) * Real.sqrt (scaleA x)) / scaleL x =
            (Real.sqrt (scaleL x) * Real.sqrt (scaleA x)) /
              (Real.sqrt (scaleL x) * Real.sqrt (scaleL x)) :=
          congrArg (fun d : ℝ =>
            (Real.sqrt (scaleL x) * Real.sqrt (scaleA x)) / d) hden
        _ = Real.sqrt (scaleA x) / Real.sqrt (scaleL x) := by
          field_simp [ne_of_gt (Real.sqrt_pos.2 hL)]
    _ = Real.sqrt (scaleA x / scaleL x) := by
      rw [Real.sqrt_div hA]

/-- One logarithm is little-o of the preceding fixed iterate.-/
theorem iteratedLog_succ_isLittleO (n : ℕ) :
    (iteratedLog (n + 1)) =o[atTop] (iteratedLog n) := by
  have h := Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_iteratedLog_atTop n)
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

theorem log4_isLittleO_log3 : log4 =o[atTop] log3 := by
  have h := iteratedLog_succ_isLittleO 3
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

theorem const_log_two_isLittleO_log3 :
    (fun _ : ℝ => Real.log 2) =o[atTop] log3 := by
  have h := (Real.isLittleO_const_log_atTop (c := Real.log 2)).comp_tendsto
    (tendsto_iteratedLog_atTop 2)
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

/-- The second-order correction in `A` is negligible relative to `log₃ x`.-/
theorem scaleA_isEquivalent_log3 : scaleA ~[atTop] log3 := by
  have herror : (fun x => log4 x - Real.log 2) =o[atTop] log3 :=
    log4_isLittleO_log3.sub const_log_two_isLittleO_log3
  have hequiv :=
    (Asymptotics.IsEquivalent.refl (u := log3) (l := atTop)).add_isLittleO herror
  apply hequiv.congr_left
  filter_upwards [] with x
  simp only [Pi.add_apply, scaleA]
  ring

theorem log3_isLittleO_scaleL : log3 =o[atTop] scaleL := by
  have h32 : (iteratedLog 3) =o[atTop] (iteratedLog 2) :=
    iteratedLog_succ_isLittleO 2
  have h21 : (iteratedLog 2) =o[atTop] (iteratedLog 1) :=
    iteratedLog_succ_isLittleO 1
  have h := h32.trans h21
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

theorem scaleA_isLittleO_scaleL : scaleA =o[atTop] scaleL :=
  scaleA_isEquivalent_log3.isBigO.trans_isLittleO log3_isLittleO_scaleL

theorem tendsto_scaleA_atTop : Tendsto scaleA atTop atTop :=
  scaleA_isEquivalent_log3.symm.tendsto_atTop tendsto_log3_atTop

theorem eventually_scaleL_pos : ∀ᶠ x in atTop, 0 < scaleL x :=
  tendsto_scaleL_atTop.eventually_gt_atTop 0

theorem eventually_scaleA_pos : ∀ᶠ x in atTop, 0 < scaleA x :=
  tendsto_scaleA_atTop.eventually_gt_atTop 0

theorem tendsto_scaleG_atTop : Tendsto scaleG atTop atTop := by
  have hprod : Tendsto (fun x => scaleL x * scaleA x) atTop atTop :=
    tendsto_scaleL_atTop.atTop_mul_atTop₀ tendsto_scaleA_atTop
  change Tendsto (fun x => Real.sqrt (scaleL x * scaleA x)) atTop atTop
  exact Real.tendsto_sqrt_atTop.comp hprod

theorem tendsto_scaleG_div_scaleL_zero :
    Tendsto (fun x => scaleG x / scaleL x) atTop (nhds 0) := by
  have hratio : Tendsto (fun x => scaleA x / scaleL x) atTop (nhds 0) :=
    scaleA_isLittleO_scaleL.tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun x => Real.sqrt (scaleA x / scaleL x)) atTop (nhds 0) := by
    simpa using hratio.sqrt
  apply hsqrt.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  exact (scaleG_div_scaleL_eq_sqrt_div hL hA.le).symm

/-- The paper's relation `G = o(L)`.-/
theorem scaleG_isLittleO_scaleL : scaleG =o[atTop] scaleL := by
  refine Asymptotics.isLittleO_of_tendsto' ?_ tendsto_scaleG_div_scaleL_zero
  filter_upwards [eventually_scaleL_pos] with x hL
  exact fun hzero => (hL.ne' hzero).elim

/-- The paper's relation `V → ∞`.-/
theorem tendsto_scaleV_atTop : Tendsto scaleV atTop atTop := by
  have hratioPos : ∀ᶠ x in atTop, 0 < scaleG x / scaleL x := by
    filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
    exact div_pos (scaleG_pos hL hA) hL
  have hratioWithin :
      Tendsto (fun x => scaleG x / scaleL x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_scaleG_div_scaleL_zero, hratioPos⟩
  have hinv : Tendsto (fun x => (scaleG x / scaleL x)⁻¹) atTop atTop :=
    hratioWithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  rw [scaleV_eq]
  field_simp [ne_of_gt hL, ne_of_gt (scaleG_pos hL hA)]

end

end RankAmplification
