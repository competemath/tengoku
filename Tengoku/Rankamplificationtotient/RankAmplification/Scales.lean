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

/--
@isnad1 id=eq.0h1v.s3.63703d6e762f from=translated src=- shape=5b483ac0 vocab=24432faa
-/
@[simp]
theorem iteratedLog_zero (x : ℝ) : iteratedLog 0 x = x := rfl

/--
@isnad1 id=eq.0h2v.s4.925c671bc764 from=translated src=- shape=442880ac vocab=3daf67fb
-/
@[simp]
theorem iteratedLog_succ (n : ℕ) (x : ℝ) :
    iteratedLog (n + 1) x = Real.log (iteratedLog n x) := rfl

/--
@isnad1 id=eq.0h1v.s3.d73a09410411 from=translated src=- shape=0600d945 vocab=46074055
-/
@[simp]
theorem iteratedLog_one (x : ℝ) : iteratedLog 1 x = Real.log x := rfl

/--
@isnad1 id=eq.0h1v.s3.b91f725fc95c from=translated src=- shape=5dad4736 vocab=16238ac3
-/
@[simp]
theorem log2_eq (x : ℝ) : log2 x = Real.log (Real.log x) := rfl

/--
@isnad1 id=eq.0h1v.s3.9b9b88be8cc5 from=translated src=- shape=5dad4736 vocab=4b323081
-/
@[simp]
theorem log3_eq (x : ℝ) : log3 x = Real.log (log2 x) := rfl

/--
@isnad1 id=eq.0h1v.s3.2f78b0a522ba from=translated src=- shape=5dad4736 vocab=7f5c4ae3
-/
@[simp]
theorem log4_eq (x : ℝ) : log4 x = Real.log (log3 x) := rfl

/--
@isnad1 id=eq.0h1v.s3.6fcca42871ce from=translated src=- shape=0fc427d2 vocab=9a535a2a
-/
@[simp]
theorem scaleL_eq (x : ℝ) : scaleL x = Real.log x := rfl

/--
@isnad1 id=eq.0h1v.s5.6cd14a42575c from=translated src=- shape=e6435884 vocab=25f38c17
-/
@[simp]
theorem scaleA_eq (x : ℝ) : scaleA x = log3 x + log4 x - Real.log 2 := rfl

/--
@isnad1 id=eq.0h1v.s4.37f96db7d963 from=translated src=- shape=5712c7f1 vocab=625d4f3c
-/
@[simp]
theorem scaleG_eq (x : ℝ) : scaleG x = Real.sqrt (scaleL x * scaleA x) := rfl

/--
@isnad1 id=eq.0h1v.s4.48c444307fce from=translated src=- shape=f108d266 vocab=4f4614f2
-/
@[simp]
theorem scaleV_eq (x : ℝ) : scaleV x = scaleL x / scaleG x := rfl

/-- Every fixed iterate of the logarithm tends to infinity.
@isnad1 id=tendsto.0h1v.s3.2aaec3b75c88 from=translated src=- shape=74931b86 vocab=f3516780
-/
theorem tendsto_iteratedLog_atTop (n : ℕ) : Tendsto (iteratedLog n) atTop atTop := by
  induction n with
  | zero => exact tendsto_id
  | succ n ih =>
      change Tendsto (fun x => Real.log (iteratedLog n x)) atTop atTop
      exact Real.tendsto_log_atTop.comp ih

/--
@isnad1 id=tendsto.0h0v.s3.2890de97e5d8 from=translated src=- shape=41b74a9e vocab=7f72c1ec
-/
theorem tendsto_log2_atTop : Tendsto log2 atTop atTop := by
  change Tendsto (iteratedLog 2) atTop atTop
  exact tendsto_iteratedLog_atTop 2

/--
@isnad1 id=tendsto.0h0v.s3.3c4033ef2430 from=translated src=- shape=41b74a9e vocab=71ca96a2
-/
theorem tendsto_log3_atTop : Tendsto log3 atTop atTop := by
  change Tendsto (iteratedLog 3) atTop atTop
  exact tendsto_iteratedLog_atTop 3

/--
@isnad1 id=tendsto.0h0v.s3.44e6ebbab035 from=translated src=- shape=41b74a9e vocab=1129c2bb
-/
theorem tendsto_log4_atTop : Tendsto log4 atTop atTop := by
  change Tendsto (iteratedLog 4) atTop atTop
  exact tendsto_iteratedLog_atTop 4

/--
@isnad1 id=tendsto.0h0v.s3.a356e8882bd8 from=translated src=- shape=41b74a9e vocab=56e15f13
-/
theorem tendsto_scaleL_atTop : Tendsto scaleL atTop atTop := by
  change Tendsto Real.log atTop atTop
  exact Real.tendsto_log_atTop

/-- Each iterated logarithm is eventually positive.
@isnad1 id=eventual.0h1v.s4.5b6dad603e44 from=translated src=- shape=67157f14 vocab=ffe8255f
-/
theorem eventually_iteratedLog_pos (n : ℕ) : ∀ᶠ x in atTop, 0 < iteratedLog n x :=
  (tendsto_iteratedLog_atTop n).eventually_gt_atTop 0

/--
@isnad1 id=eventual.0h0v.s4.8ccc6e4893e4 from=translated src=- shape=012bd729 vocab=9d258174
-/
theorem eventually_log2_pos : ∀ᶠ x in atTop, 0 < log2 x :=
  tendsto_log2_atTop.eventually_gt_atTop 0

/--
@isnad1 id=eventual.0h0v.s4.cd0b03d9758c from=translated src=- shape=012bd729 vocab=79d2ff9a
-/
theorem eventually_log3_pos : ∀ᶠ x in atTop, 0 < log3 x :=
  tendsto_log3_atTop.eventually_gt_atTop 0

/--
@isnad1 id=eventual.0h0v.s4.8552c5e091e9 from=translated src=- shape=012bd729 vocab=be41c1c5
-/
theorem eventually_log4_pos : ∀ᶠ x in atTop, 0 < log4 x :=
  tendsto_log4_atTop.eventually_gt_atTop 0

/--
@isnad1 id=lt.1h1v.s4.03a68a18dbc0 from=translated src=- shape=35bd48ee vocab=8b54bc4b
-/
theorem scaleL_pos {x : ℝ} (hx : 1 < x) : 0 < scaleL x :=
  Real.log_pos hx

/--
@isnad1 id=lt.1h1v.s4.66de1ed1de73 from=translated src=- shape=3eced894 vocab=82bbbdc1
-/
theorem log2_pos {x : ℝ} (hx : 1 < Real.log x) : 0 < log2 x := by
  rw [log2_eq]
  exact Real.log_pos hx

/--
@isnad1 id=lt.1h1v.s4.4579e3357972 from=translated src=- shape=3eced894 vocab=424b961f
-/
theorem log3_pos {x : ℝ} (hx : 1 < log2 x) : 0 < log3 x := by
  rw [log3_eq]
  exact Real.log_pos hx

/--
@isnad1 id=lt.1h1v.s4.86200c5f44e3 from=translated src=- shape=3eced894 vocab=55a97222
-/
theorem log4_pos {x : ℝ} (hx : 1 < log3 x) : 0 < log4 x := by
  rw [log4_eq]
  exact Real.log_pos hx

/--
@isnad1 id=lt.1h1v.s5.2507fc468e44 from=translated src=- shape=6f4107c9 vocab=e492b0b5
-/
theorem scaleA_pos {x : ℝ} (hx : Real.log 2 < log3 x + log4 x) : 0 < scaleA x := by
  simpa only [scaleA_eq, sub_pos] using hx

/--
@isnad1 id=le.1h1v.s5.d7242d47445c from=translated src=- shape=6f4107c9 vocab=b9f1eb15
-/
theorem scaleA_nonneg {x : ℝ} (hx : Real.log 2 ≤ log3 x + log4 x) : 0 ≤ scaleA x := by
  simpa only [scaleA_eq, sub_nonneg] using hx

/--
@isnad1 id=le.0h1v.s3.bf673e5bbccf from=translated src=- shape=8a62b088 vocab=8025ff85
-/
theorem scaleG_nonneg (x : ℝ) : 0 ≤ scaleG x :=
  Real.sqrt_nonneg _

/--
@isnad1 id=lt.2h1v.s5.0d918d18f145 from=translated src=- shape=aaad930a vocab=e45acfe1
-/
theorem scaleG_pos {x : ℝ} (hL : 0 < scaleL x) (hA : 0 < scaleA x) : 0 < scaleG x := by
  rw [scaleG_eq, Real.sqrt_pos]
  exact mul_pos hL hA

/--
@isnad1 id=lt.2h1v.s5.0173a7d08136 from=translated src=- shape=aaad930a vocab=16c6467a
-/
theorem scaleV_pos {x : ℝ} (hL : 0 < scaleL x) (hG : 0 < scaleG x) : 0 < scaleV x := by
  rw [scaleV_eq]
  exact div_pos hL hG

/-- Squaring `G` recovers `L A` in the nonnegative range.
@isnad1 id=eq.2h1v.s5.94aaf166e466 from=translated src=- shape=f0227ffc vocab=c2390bf4
-/
theorem scaleG_sq {x : ℝ} (hL : 0 ≤ scaleL x) (hA : 0 ≤ scaleA x) :
    scaleG x ^ 2 = scaleL x * scaleA x := by
  rw [scaleG_eq, Real.sq_sqrt (mul_nonneg hL hA)]

/-- The defining cancellation `G V = L`.
@isnad1 id=eq.1h1v.s4.92c734bea195 from=translated src=- shape=14456bfe vocab=c1e8c029
-/
theorem scaleG_mul_scaleV {x : ℝ} (hG : scaleG x ≠ 0) :
    scaleG x * scaleV x = scaleL x := by
  rw [scaleV_eq]
  exact mul_div_cancel₀ _ hG

/--
@isnad1 id=eq.1h1v.s4.aa7401544995 from=translated src=- shape=293bdbc0 vocab=c1e8c029
-/
theorem scaleV_mul_scaleG {x : ℝ} (hG : scaleG x ≠ 0) :
    scaleV x * scaleG x = scaleL x := by
  rw [mul_comm]
  exact scaleG_mul_scaleV hG

/-- In the positive range, `A V = G`.
@isnad1 id=eq.3h1v.s5.ce3566f8c482 from=translated src=- shape=5d0f4564 vocab=ffbbea40
-/
theorem scaleA_mul_scaleV {x : ℝ} (hL : 0 ≤ scaleL x) (hA : 0 ≤ scaleA x)
    (hG : scaleG x ≠ 0) : scaleA x * scaleV x = scaleG x := by
  rw [scaleV_eq]
  have hsq := scaleG_sq hL hA
  field_simp
  nlinarith

/-- In the positive range, `G / V = A`.
@isnad1 id=eq.3h1v.s5.a13795b0bf04 from=translated src=- shape=86b2232a vocab=a2d77510
-/
theorem scaleG_div_scaleV {x : ℝ} (hL : 0 < scaleL x) (hA : 0 ≤ scaleA x)
    (hG : scaleG x ≠ 0) : scaleG x / scaleV x = scaleA x := by
  rw [scaleV_eq]
  have hsq := scaleG_sq hL.le hA
  have hG' : 0 ≠ scaleG x := hG.symm
  field_simp [hG', ne_of_gt hL]
  nlinarith

/-- The quotient `G/L` is the square root of `A/L` in the positive range.
@isnad1 id=eq.2h1v.s5.8c94e04ca877 from=translated src=- shape=3cbeff83 vocab=2dcd43b7
-/
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

/-- One logarithm is little-o of the preceding fixed iterate.
@isnad1 id=islittle.0h1v.s4.8785399a6fae from=translated src=- shape=f6b89769 vocab=fb7a30ac
-/
theorem iteratedLog_succ_isLittleO (n : ℕ) :
    (iteratedLog (n + 1)) =o[atTop] (iteratedLog n) := by
  have h := Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_iteratedLog_atTop n)
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

/--
@isnad1 id=islittle.0h0v.s3.8d99bb48b28e from=translated src=- shape=47806ae7 vocab=ce0f6548
-/
theorem log4_isLittleO_log3 : log4 =o[atTop] log3 := by
  have h := iteratedLog_succ_isLittleO 3
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

/--
@isnad1 id=islittle.0h0v.s4.3de47407cc54 from=translated src=- shape=e20bc3b3 vocab=ed848230
-/
theorem const_log_two_isLittleO_log3 :
    (fun _ : ℝ => Real.log 2) =o[atTop] log3 := by
  have h := (Real.isLittleO_const_log_atTop (c := Real.log 2)).comp_tendsto
    (tendsto_iteratedLog_atTop 2)
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

/-- The second-order correction in `A` is negligible relative to `log₃ x`.
@isnad1 id=isequiva.0h0v.s4.1c805cacc05b from=translated src=- shape=62461370 vocab=3068fc96
-/
theorem scaleA_isEquivalent_log3 : scaleA ~[atTop] log3 := by
  have herror : (fun x => log4 x - Real.log 2) =o[atTop] log3 :=
    log4_isLittleO_log3.sub const_log_two_isLittleO_log3
  have hequiv :=
    (Asymptotics.IsEquivalent.refl (u := log3) (l := atTop)).add_isLittleO herror
  apply hequiv.congr_left
  filter_upwards [] with x
  simp only [Pi.add_apply, scaleA]
  ring

/--
@isnad1 id=islittle.0h0v.s3.7fd43bd153ab from=translated src=- shape=47806ae7 vocab=6e1bc32d
-/
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

/--
@isnad1 id=islittle.0h0v.s3.6c58fe1163f8 from=translated src=- shape=47806ae7 vocab=40314829
-/
theorem scaleA_isLittleO_scaleL : scaleA =o[atTop] scaleL :=
  scaleA_isEquivalent_log3.isBigO.trans_isLittleO log3_isLittleO_scaleL

/--
@isnad1 id=tendsto.0h0v.s3.d447747059f5 from=translated src=- shape=41b74a9e vocab=b47bf463
-/
theorem tendsto_scaleA_atTop : Tendsto scaleA atTop atTop :=
  scaleA_isEquivalent_log3.symm.tendsto_atTop tendsto_log3_atTop

/--
@isnad1 id=eventual.0h0v.s4.f6e6000a0d36 from=translated src=- shape=012bd729 vocab=2663c4de
-/
theorem eventually_scaleL_pos : ∀ᶠ x in atTop, 0 < scaleL x :=
  tendsto_scaleL_atTop.eventually_gt_atTop 0

/--
@isnad1 id=eventual.0h0v.s4.f9d04795a77f from=translated src=- shape=012bd729 vocab=7118615d
-/
theorem eventually_scaleA_pos : ∀ᶠ x in atTop, 0 < scaleA x :=
  tendsto_scaleA_atTop.eventually_gt_atTop 0

/--
@isnad1 id=tendsto.0h0v.s3.8665ecfeb78e from=translated src=- shape=41b74a9e vocab=ede3e904
-/
theorem tendsto_scaleG_atTop : Tendsto scaleG atTop atTop := by
  have hprod : Tendsto (fun x => scaleL x * scaleA x) atTop atTop :=
    tendsto_scaleL_atTop.atTop_mul_atTop₀ tendsto_scaleA_atTop
  change Tendsto (fun x => Real.sqrt (scaleL x * scaleA x)) atTop atTop
  exact Real.tendsto_sqrt_atTop.comp hprod

/--
@isnad1 id=tendsto.0h0v.s5.edfcefbd2db9 from=translated src=- shape=93a4dec3 vocab=a1a82ee8
-/
theorem tendsto_scaleG_div_scaleL_zero :
    Tendsto (fun x => scaleG x / scaleL x) atTop (nhds 0) := by
  have hratio : Tendsto (fun x => scaleA x / scaleL x) atTop (nhds 0) :=
    scaleA_isLittleO_scaleL.tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun x => Real.sqrt (scaleA x / scaleL x)) atTop (nhds 0) := by
    simpa using hratio.sqrt
  apply hsqrt.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  exact (scaleG_div_scaleL_eq_sqrt_div hL hA.le).symm

/-- The paper's relation `G = o(L)`.
@isnad1 id=islittle.0h0v.s3.f1933aed99e6 from=translated src=- shape=47806ae7 vocab=a817ba9e
-/
theorem scaleG_isLittleO_scaleL : scaleG =o[atTop] scaleL := by
  refine Asymptotics.isLittleO_of_tendsto' ?_ tendsto_scaleG_div_scaleL_zero
  filter_upwards [eventually_scaleL_pos] with x hL
  exact fun hzero => (hL.ne' hzero).elim

/-- The paper's relation `V → ∞`.
@isnad1 id=tendsto.0h0v.s3.6d1af65dead7 from=translated src=- shape=41b74a9e vocab=1e807c06
-/
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
