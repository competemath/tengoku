import Tengoku.Rankamplificationtotient.RankAmplification.Scales
import Tengoku.Seed.Analysis.Asymptotics.SpecificAsymptotics
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.Algebra.Order.Floor.Semifield

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Moving-rank scales This module formalizes the parameters introduced in (10.21)--(10.22). -/

namespace RankAmplification

open Filter
open Asymptotics
open scoped Asymptotics Topology

noncomputable section

/-! ## Definitions (10.21)--(10.22), in dependency order -/

/-- The moving scale `R = sqrt(L L₂)`.-/
def movingR (x : ℝ) : ℝ := Real.sqrt (scaleL x * log2 x)

/-- The moving perturbation `η = A⁻¹⁄²`.-/
def movingEta (x : ℝ) : ℝ := (Real.sqrt (scaleA x))⁻¹

/-- The intermediate exponent `E = (1/2 - η)R`.-/
def movingE (x : ℝ) : ℝ := (1 / 2 - movingEta x) * movingR x

/-- The target exponent before flooring, `K₀ = (1/2 - 2η)R`.-/
def movingK0 (x : ℝ) : ℝ := (1 / 2 - 2 * movingEta x) * movingR x

/-- The source cutoff logarithm `T = LA/(2E)`.-/
def movingT (x : ℝ) : ℝ := scaleL x * scaleA x / (2 * movingE x)

/-- The real quotient which is floored to obtain the moving rank.-/
def movingRankQuotient (x : ℝ) : ℝ := movingK0 x / movingT x

/-- The moving rank `J = floor(K₀/T)`.-/
def movingJ (x : ℝ) : ℕ := ⌊movingRankQuotient x⌋₊

/-- The actual exponent `K = JT`.-/
def movingK (x : ℝ) : ℝ := (movingJ x : ℝ) * movingT x

/-- The lower prime cutoff `y = exp T`.-/
def movingY (x : ℝ) : ℝ := Real.exp (movingT x)

/-- The upper prime cutoff `Z = exp K`.-/
def movingZ (x : ℝ) : ℝ := Real.exp (movingK x)

/--
@isnad1 id=eq.0h1v.s3.b91406b5cf8e from=translated src=- shape=5dad4736 vocab=30d9bbc2
-/
@[simp] theorem movingY_eq_exp (x : ℝ) : movingY x = Real.exp (movingT x) := rfl
/--
@isnad1 id=eq.0h1v.s3.dd3c9ef37d9f from=translated src=- shape=5dad4736 vocab=212b9621
-/
@[simp] theorem movingZ_eq_exp (x : ℝ) : movingZ x = Real.exp (movingK x) := rfl
/--
@isnad1 id=eq.0h1v.s3.889d26436ba7 from=translated src=- shape=c52356c6 vocab=742b527f
-/
@[simp, nolint simpNF] theorem log_movingY (x : ℝ) : Real.log (movingY x) = movingT x := by
  rw [movingY, Real.log_exp]
/--
@isnad1 id=eq.0h1v.s3.7cb06a20f9e5 from=translated src=- shape=c52356c6 vocab=e5221daa
-/
@[simp, nolint simpNF] theorem log_movingZ (x : ℝ) : Real.log (movingZ x) = movingK x := by
  rw [movingZ, Real.log_exp]
/--
@isnad1 id=eq.0h1v.s4.0a259bd32760 from=translated src=- shape=1b5ddb25 vocab=8fb34d83
-/
@[simp] theorem movingJ_eq_floor (x : ℝ) : movingJ x = ⌊movingK0 x / movingT x⌋₊ := rfl
/--
@isnad1 id=eq.0h1v.s4.dc44aafacae9 from=translated src=- shape=409b6d87 vocab=049ce1ea
-/
@[simp] theorem movingK_eq_rank_mul (x : ℝ) :
    movingK x = (movingJ x : ℝ) * movingT x := rfl

/-! ## Positivity and exact algebra -/

/--
@isnad1 id=eq.2h1v.s5.d582604ce48b from=translated src=- shape=f0227ffc vocab=b2a35994
-/
theorem movingR_sq {x : ℝ} (hL : 0 ≤ scaleL x) (hL2 : 0 ≤ log2 x) :
    movingR x ^ 2 = scaleL x * log2 x := by
  rw [movingR, Real.sq_sqrt (mul_nonneg hL hL2)]

/--
@isnad1 id=lt.2h1v.s5.a7952f14a80a from=translated src=- shape=aaad930a vocab=a7bb0120
-/
theorem movingR_pos {x : ℝ} (hL : 0 < scaleL x) (hL2 : 0 < log2 x) :
    0 < movingR x := by
  rw [movingR, Real.sqrt_pos]
  exact mul_pos hL hL2

/--
@isnad1 id=lt.1h1v.s4.b62457ba3f33 from=translated src=- shape=3eced894 vocab=87b5efc9
-/
theorem movingEta_pos {x : ℝ} (hA : 0 < scaleA x) :
    0 < movingEta x := by
  exact inv_pos.mpr (Real.sqrt_pos.2 hA)

/--
@isnad1 id=lt.2h1v.s5.d60efc1673a6 from=translated src=- shape=1fa1e28d vocab=eb48faf5
-/
theorem movingE_pos {x : ℝ} (hR : 0 < movingR x) (heta : movingEta x < 1 / 2) :
    0 < movingE x := by
  unfold movingE
  exact mul_pos (sub_pos.mpr heta) hR

/--
@isnad1 id=lt.2h1v.s5.7b21204d9c11 from=translated src=- shape=1fa1e28d vocab=7e2c9290
-/
theorem movingK0_pos {x : ℝ} (hR : 0 < movingR x) (heta : movingEta x < 1 / 4) :
    0 < movingK0 x := by
  unfold movingK0
  apply mul_pos _ hR
  linarith

/--
@isnad1 id=lt.3h1v.s5.9ed31ece7dc0 from=translated src=- shape=b49d77b0 vocab=a3c5f1b0
-/
theorem movingT_pos {x : ℝ} (hL : 0 < scaleL x) (hA : 0 < scaleA x)
    (hE : 0 < movingE x) :
    0 < movingT x := by
  unfold movingT
  positivity

/-- The natural floor lies below its defining nonnegative quotient.
@isnad1 id=le.1h1v.s4.00378f07ffec from=translated src=- shape=2c39f7be vocab=41cdd286
-/
theorem movingJ_cast_le_rankQuotient {x : ℝ} (hq : 0 ≤ movingRankQuotient x) :
    (movingJ x : ℝ) ≤ movingRankQuotient x := by
  exact Nat.floor_le hq

/-- The strict upper floor inequality, valid without a sign premise.
@isnad1 id=lt.0h1v.s4.cd2a12b79fb5 from=translated src=- shape=7efad882 vocab=db4adedb
-/
theorem movingRankQuotient_lt_movingJ_add_one (x : ℝ) :
    movingRankQuotient x < (movingJ x : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

/--
@isnad1 id=and.1h1v.s5.a4af4d2f552f from=translated src=- shape=7f7b2f98 vocab=ab9993ba
-/
theorem movingJ_le_rankQuotient_lt_add_one {x : ℝ}
    (hq : 0 ≤ movingRankQuotient x) :
    (movingJ x : ℝ) ≤ movingRankQuotient x ∧
      movingRankQuotient x < (movingJ x : ℝ) + 1 :=
  ⟨movingJ_cast_le_rankQuotient hq, movingRankQuotient_lt_movingJ_add_one x⟩

/-- Exact floor identity: the pre-floor exponent is the quotient times `T`.
@isnad1 id=eq.1h1v.s4.da9980487bc0 from=translated src=- shape=293bdbc0 vocab=24fa9623
-/
theorem movingRankQuotient_mul_T {x : ℝ} (hT : movingT x ≠ 0) :
    movingRankQuotient x * movingT x = movingK0 x := by
  unfold movingRankQuotient
  exact div_mul_cancel₀ _ hT

/-- The complete rounding estimate `0 ≤ K₀-K < T`.
@isnad1 id=and.2h1v.s5.b448527033b7 from=translated src=- shape=14295d1a vocab=01b078d2
-/
theorem movingK_floor_error {x : ℝ} (hT : 0 < movingT x) (hK0 : 0 ≤ movingK0 x) :
    0 ≤ movingK0 x - movingK x ∧ movingK0 x - movingK x < movingT x := by
  have hq : 0 ≤ movingRankQuotient x := div_nonneg hK0 hT.le
  have hlower := movingJ_cast_le_rankQuotient hq
  have hupper := movingRankQuotient_lt_movingJ_add_one x
  have hidentity := movingRankQuotient_mul_T hT.ne'
  constructor
  · rw [movingK, ← hidentity]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hlower hT.le)
  · rw [movingK, ← hidentity]
    have := mul_lt_mul_of_pos_right hupper hT
    nlinarith

/--
@isnad1 id=le.2h1v.s5.00c3b9e53784 from=translated src=- shape=575bcaa1 vocab=38e5293c
-/
theorem movingK_le_K0 {x : ℝ} (hT : 0 < movingT x) (hK0 : 0 ≤ movingK0 x) :
    movingK x ≤ movingK0 x :=
  sub_nonneg.mp (movingK_floor_error hT hK0).1

/-! ## Elementary limits of the moving scales -/

/--
@isnad1 id=islittle.0h0v.s3.63db79f841bb from=translated src=- shape=47806ae7 vocab=e047fdbd
-/
theorem log2_isLittleO_scaleL : log2 =o[atTop] scaleL := by
  have h := iteratedLog_succ_isLittleO 1
  apply h.congr'
  · filter_upwards [] with x
    rfl
  · filter_upwards [] with x
    rfl

/--
@isnad1 id=islittle.0h0v.s3.96c284cd4959 from=translated src=- shape=47806ae7 vocab=f4ba70e2
-/
theorem scaleA_isLittleO_log2 : scaleA =o[atTop] log2 := by
  have h32 : log3 =o[atTop] log2 := by
    have h := iteratedLog_succ_isLittleO 2
    apply h.congr'
    · filter_upwards [] with x
      rfl
    · filter_upwards [] with x
      rfl
  exact scaleA_isEquivalent_log3.isBigO.trans_isLittleO h32

/--
@isnad1 id=tendsto.0h0v.s4.e1707e54d659 from=translated src=- shape=95bb6042 vocab=20e9b77b
-/
theorem tendsto_movingEta_zero : Tendsto movingEta atTop (nhds 0) := by
  change Tendsto (fun x ↦ (Real.sqrt (scaleA x))⁻¹) atTop (nhds 0)
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_scaleA_atTop)

/--
@isnad1 id=eventual.1h1v.s4.0b45f66bfb0d from=translated src=- shape=b2128ae1 vocab=3fca960c
-/
theorem eventually_movingEta_lt (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x in atTop, movingEta x < c := by
  have h := tendsto_movingEta_zero.eventually (Iio_mem_nhds hc)
  simpa using h

/--
@isnad1 id=tendsto.0h0v.s3.7e1d27a12abf from=translated src=- shape=41b74a9e vocab=7b804a48
-/
theorem tendsto_movingR_atTop : Tendsto movingR atTop atTop := by
  have hprod : Tendsto (fun x ↦ scaleL x * log2 x) atTop atTop :=
    tendsto_scaleL_atTop.atTop_mul_atTop₀ tendsto_log2_atTop
  exact Real.tendsto_sqrt_atTop.comp hprod

/--
@isnad1 id=tendsto.0h0v.s4.be9ddcc153a5 from=translated src=- shape=53861ef7 vocab=4200b29b
-/
theorem tendsto_scaleL_div_log2_atTop :
    Tendsto (fun x ↦ scaleL x / log2 x) atTop atTop := by
  have hzero : Tendsto (fun x ↦ log2 x / scaleL x) atTop (nhds 0) :=
    log2_isLittleO_scaleL.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x in atTop, 0 < log2 x / scaleL x := by
    filter_upwards [eventually_log2_pos, eventually_scaleL_pos] with x hL2 hL
    exact div_pos hL2 hL
  have hwithin : Tendsto (fun x ↦ log2 x / scaleL x) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_log2_pos, eventually_scaleL_pos] with x hL2 hL
  change (log2 x / scaleL x)⁻¹ = scaleL x / log2 x
  rw [inv_div]

/--
@isnad1 id=tendsto.0h0v.s4.ceb0977b1ecb from=translated src=- shape=53861ef7 vocab=0fc76704
-/
theorem tendsto_log2_div_scaleA_atTop :
    Tendsto (fun x ↦ log2 x / scaleA x) atTop atTop := by
  have hzero : Tendsto (fun x ↦ scaleA x / log2 x) atTop (nhds 0) :=
    scaleA_isLittleO_log2.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x in atTop, 0 < scaleA x / log2 x := by
    filter_upwards [eventually_scaleA_pos, eventually_log2_pos] with x hA hL2
    exact div_pos hA hL2
  have hwithin : Tendsto (fun x ↦ scaleA x / log2 x) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_scaleA_pos, eventually_log2_pos] with x hA hL2
  change (scaleA x / log2 x)⁻¹ = log2 x / scaleA x
  rw [inv_div]

/--
@isnad1 id=eventual.0h0v.s6.f47f783e460b from=translated src=- shape=0b5f3cd7 vocab=0c777489
-/
theorem eventually_moving_core_positive :
    ∀ᶠ x in atTop,
      0 < scaleL x ∧ 0 < log2 x ∧ 0 < scaleA x ∧
      0 < movingR x ∧ 0 < movingEta x ∧
      0 < movingE x ∧ 0 < movingK0 x ∧ 0 < movingT x := by
  filter_upwards [eventually_scaleL_pos, eventually_log2_pos, eventually_scaleA_pos,
      eventually_movingEta_lt (1 / 4) (by norm_num)] with x hL hL2 hA heta
  have hR := movingR_pos hL hL2
  have hetaPos := movingEta_pos hA
  have hE := movingE_pos hR (heta.trans (by norm_num))
  have hK0 := movingK0_pos hR heta
  exact ⟨hL, hL2, hA, hR, hetaPos, hE, hK0, movingT_pos hL hA hE⟩

/-! ## Lemma 10.15: principal asymptotics -/

/-- Principal term in (10.23) for `T`.-/
def movingTMain (x : ℝ) : ℝ :=
  scaleA x * Real.sqrt (scaleL x / log2 x)

/-- Principal term in (10.23) for `J`.-/
def movingJMain (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (log2 x / scaleA x)

/--
@isnad1 id=eq.2h1v.s5.124999883380 from=translated src=- shape=eb15cc4f vocab=93516ab6
-/
theorem scaleL_div_movingR_eq_sqrt_div {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) :
    scaleL x / movingR x = Real.sqrt (scaleL x / log2 x) := by
  rw [movingR, Real.sqrt_mul hL.le]
  calc
    scaleL x / (Real.sqrt (scaleL x) * Real.sqrt (log2 x)) =
        (Real.sqrt (scaleL x) * Real.sqrt (scaleL x)) /
          (Real.sqrt (scaleL x) * Real.sqrt (log2 x)) := by
      rw [Real.mul_self_sqrt hL.le]
    _ = Real.sqrt (scaleL x) / Real.sqrt (log2 x) := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 hL), ne_of_gt (Real.sqrt_pos.2 hL2)]
    _ = Real.sqrt (scaleL x / log2 x) := by
      rw [Real.sqrt_div hL.le]

/--
@isnad1 id=eq.2h1v.s5.0c1f8260f385 from=translated src=- shape=38a157ef vocab=93516ab6
-/
theorem movingR_div_sqrt_div_eq_log2 {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) :
    movingR x / Real.sqrt (scaleL x / log2 x) = log2 x := by
  have hroot : 0 < Real.sqrt (scaleL x / log2 x) := by
    rw [Real.sqrt_pos]
    exact div_pos hL hL2
  have hR := movingR_pos hL hL2
  have hRsq := movingR_sq hL.le hL2.le
  have hrootSq : Real.sqrt (scaleL x / log2 x) ^ 2 = scaleL x / log2 x :=
    Real.sq_sqrt (div_nonneg hL.le hL2.le)
  have hsq : (log2 x * Real.sqrt (scaleL x / log2 x)) ^ 2 = movingR x ^ 2 := by
    rw [mul_pow, hrootSq, hRsq]
    field_simp [hL2.ne']
  have heq : movingR x = log2 x * Real.sqrt (scaleL x / log2 x) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq.symm with heq | heq
    · exact heq
    · exfalso
      nlinarith [mul_pos hL2 hroot]
  exact (div_eq_iff hroot.ne').mpr heq

/--
@isnad1 id=eq.3h1v.s6.bf484823566b from=translated src=- shape=5fd6100b vocab=e518afe7
-/
theorem movingT_eq_main_div {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x)
    (heta : movingEta x < 1 / 2) :
    movingT x = movingTMain x / (1 - 2 * movingEta x) := by
  have hR := movingR_pos hL hL2
  have hcoef : 1 - 2 * movingEta x ≠ 0 := by linarith
  rw [movingT, movingE, movingTMain,
    ← scaleL_div_movingR_eq_sqrt_div hL hL2]
  field_simp [hR.ne', hcoef]

/--
@isnad1 id=tendsto.0h0v.s4.8dfe1b028d6c from=translated src=- shape=de249496 vocab=147e8777
-/
theorem tendsto_sqrt_scaleL_div_log2_atTop :
    Tendsto (fun x ↦ Real.sqrt (scaleL x / log2 x)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_scaleL_div_log2_atTop

/--
@isnad1 id=tendsto.0h0v.s3.515ff31e2f09 from=translated src=- shape=41b74a9e vocab=94794519
-/
theorem tendsto_movingTMain_atTop : Tendsto movingTMain atTop atTop := by
  exact tendsto_scaleA_atTop.atTop_mul_atTop₀ tendsto_sqrt_scaleL_div_log2_atTop

/-- Equation (10.23): `T ~ A sqrt(L/L₂)`.
@isnad1 id=isequiva.0h0v.s4.2c39829b8d80 from=translated src=- shape=62461370 vocab=a9bae22d
-/
theorem movingT_isEquivalent_main : movingT ~[atTop] movingTMain := by
  apply isEquivalent_of_tendsto_one
  have hfactor : Tendsto (fun x ↦ (1 - 2 * movingEta x)⁻¹) atTop (nhds 1) := by
    have hden : Tendsto (fun x ↦ 1 - 2 * movingEta x) atTop (nhds 1) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_movingEta_zero) using 1
      norm_num
    simpa using hden.inv₀ (by norm_num)
  apply hfactor.congr'
  filter_upwards [eventually_moving_core_positive,
      eventually_movingEta_lt (1 / 2) (by norm_num)] with x hcore heta
  change (1 - 2 * movingEta x)⁻¹ = movingT x / movingTMain x
  rw [movingT_eq_main_div hcore.1 hcore.2.1 heta]
  have hmain : movingTMain x ≠ 0 := by
    unfold movingTMain
    exact mul_ne_zero hcore.2.2.1.ne'
      (ne_of_gt (Real.sqrt_pos.2 (div_pos hcore.1 hcore.2.1)))
  field_simp [hmain]

/--
@isnad1 id=tendsto.0h0v.s3.a6087a391614 from=translated src=- shape=41b74a9e vocab=24566845
-/
theorem tendsto_movingT_atTop : Tendsto movingT atTop atTop :=
  movingT_isEquivalent_main.symm.tendsto_atTop tendsto_movingTMain_atTop

/-- `K₀` has principal term `R/2`.
@isnad1 id=isequiva.0h0v.s5.24ddb895f785 from=translated src=- shape=d9db04d6 vocab=a169fb94
-/
theorem movingK0_isEquivalent_half_R :
    movingK0 ~[atTop] (fun x ↦ (1 / 2 : ℝ) * movingR x) := by
  apply isEquivalent_of_tendsto_one
  have hlimit : Tendsto (fun x ↦ 1 - 4 * movingEta x) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_movingEta_zero) using 1
    norm_num
  apply hlimit.congr'
  filter_upwards [eventually_moving_core_positive] with x hcore
  change 1 - 4 * movingEta x = movingK0 x / ((1 / 2 : ℝ) * movingR x)
  unfold movingK0
  have hR : movingR x ≠ 0 := hcore.2.2.2.1.ne'
  field_simp [hR]
  ring

/--
@isnad1 id=isequiva.0h0v.s4.e844e133270e from=translated src=- shape=62461370 vocab=777c6866
-/
theorem movingRankQuotient_isEquivalent_main :
    movingRankQuotient ~[atTop] movingJMain := by
  have hquot := movingK0_isEquivalent_half_R.div movingT_isEquivalent_main
  apply hquot.congr_right
  filter_upwards [eventually_moving_core_positive] with x hcore
  change ((1 / 2 : ℝ) * movingR x) / movingTMain x = movingJMain x
  unfold movingJMain movingTMain
  have hA : scaleA x ≠ 0 := hcore.2.2.1.ne'
  have hsqrt : Real.sqrt (scaleL x / log2 x) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hcore.1 hcore.2.1))
  calc
    ((1 / 2 : ℝ) * movingR x) /
        (scaleA x * Real.sqrt (scaleL x / log2 x)) =
        (1 / 2 : ℝ) *
          (movingR x / Real.sqrt (scaleL x / log2 x)) / scaleA x := by
      field_simp [hA, hsqrt]
    _ = (1 / 2 : ℝ) * (log2 x / scaleA x) := by
      rw [movingR_div_sqrt_div_eq_log2 hcore.1 hcore.2.1]
      ring

/--
@isnad1 id=tendsto.0h0v.s3.e1f3966d95e6 from=translated src=- shape=41b74a9e vocab=f37c45e3
-/
theorem tendsto_movingJMain_atTop : Tendsto movingJMain atTop atTop := by
  unfold movingJMain
  exact tendsto_log2_div_scaleA_atTop.const_mul_atTop (by norm_num)

/--
@isnad1 id=tendsto.0h0v.s3.d3b611efc5e7 from=translated src=- shape=41b74a9e vocab=e696bfa9
-/
theorem tendsto_movingRankQuotient_atTop :
    Tendsto movingRankQuotient atTop atTop :=
  movingRankQuotient_isEquivalent_main.symm.tendsto_atTop tendsto_movingJMain_atTop

/-- The natural floor is asymptotically invisible.
@isnad1 id=isequiva.0h0v.s4.27c2a75a0a92 from=translated src=- shape=f7d608ea vocab=b4cbcc15
-/
theorem movingJ_cast_isEquivalent_rankQuotient :
    (fun x ↦ (movingJ x : ℝ)) ~[atTop] movingRankQuotient := by
  apply isEquivalent_of_tendsto_one
  change Tendsto
    (fun x ↦ (⌊movingRankQuotient x⌋₊ : ℝ) / movingRankQuotient x)
    atTop (nhds 1)
  exact tendsto_nat_floor_div_atTop.comp tendsto_movingRankQuotient_atTop

/-- Equation (10.23): `J ~ (1/2)L₂/A`.
@isnad1 id=isequiva.0h0v.s4.205efe9ad9c7 from=translated src=- shape=f7d608ea vocab=f91a053d
-/
theorem movingJ_isEquivalent_main :
    (fun x ↦ (movingJ x : ℝ)) ~[atTop] movingJMain :=
  movingJ_cast_isEquivalent_rankQuotient.trans movingRankQuotient_isEquivalent_main

/--
@isnad1 id=tendsto.0h0v.s3.3bc54c12f6d5 from=translated src=- shape=57d238ad vocab=a6eb4d7a
-/
theorem tendsto_movingJ_atTop : Tendsto movingJ atTop atTop := by
  change Tendsto (fun x ↦ ⌊movingRankQuotient x⌋₊) atTop atTop
  exact tendsto_nat_floor_atTop.comp tendsto_movingRankQuotient_atTop

/--
@isnad1 id=eventual.0h0v.s4.07a86583642f from=translated src=- shape=574b785d vocab=15003b53
-/
theorem eventually_two_le_movingJ : ∀ᶠ x in atTop, 2 ≤ movingJ x :=
  tendsto_movingJ_atTop.eventually_ge_atTop 2

/-- The product of the two principal terms is exactly `R/2`.
@isnad1 id=eq.3h1v.s6.5b2cd3178693 from=translated src=- shape=3a009672 vocab=49854e85
-/
theorem movingJMain_mul_movingTMain {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) (hA : 0 < scaleA x) :
    movingJMain x * movingTMain x = (1 / 2 : ℝ) * movingR x := by
  have hsqrt : Real.sqrt (scaleL x / log2 x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (div_pos hL hL2))
  have hproduct : log2 x * Real.sqrt (scaleL x / log2 x) = movingR x := by
    exact ((div_eq_iff hsqrt).mp (movingR_div_sqrt_div_eq_log2 hL hL2)).symm
  unfold movingJMain movingTMain
  calc
    (1 / 2 : ℝ) * (log2 x / scaleA x) *
        (scaleA x * Real.sqrt (scaleL x / log2 x)) =
        (1 / 2 : ℝ) *
          (log2 x * Real.sqrt (scaleL x / log2 x)) := by
      field_simp [hA.ne']
    _ = (1 / 2 : ℝ) * movingR x := by rw [hproduct]

/-- Equation (10.24), in asymptotic-equivalence form: `K ~ K₀`.
@isnad1 id=isequiva.0h0v.s4.e61cdafde208 from=translated src=- shape=62461370 vocab=e0e44028
-/
theorem movingK_isEquivalent_K0 : movingK ~[atTop] movingK0 := by
  have hprod := movingJ_isEquivalent_main.mul movingT_isEquivalent_main
  have hhalf :
      (fun x ↦ (movingJ x : ℝ) * movingT x) ~[atTop]
        (fun x ↦ (1 / 2 : ℝ) * movingR x) := by
    apply hprod.congr_right
    filter_upwards [eventually_moving_core_positive] with x hcore
    exact movingJMain_mul_movingTMain hcore.1 hcore.2.1 hcore.2.2.1
  exact hhalf.trans movingK0_isEquivalent_half_R.symm

/--
@isnad1 id=isequiva.0h0v.s5.8fd6a7d95d92 from=translated src=- shape=d9db04d6 vocab=b2adae68
-/
theorem movingK_isEquivalent_half_R :
    movingK ~[atTop] (fun x ↦ (1 / 2 : ℝ) * movingR x) :=
  movingK_isEquivalent_K0.trans movingK0_isEquivalent_half_R

/--
@isnad1 id=tendsto.0h0v.s3.e69f0b2b59fb from=translated src=- shape=41b74a9e vocab=8a9aefb5
-/
theorem tendsto_movingK_atTop : Tendsto movingK atTop atTop := by
  have hhalf : Tendsto (fun x ↦ (1 / 2 : ℝ) * movingR x) atTop atTop :=
    tendsto_movingR_atTop.const_mul_atTop (by norm_num)
  exact movingK_isEquivalent_half_R.symm.tendsto_atTop hhalf

/-- The leading constant `1/2` in Theorem 1.4.
@isnad1 id=tendsto.0h0v.s5.ade48e9cdfcd from=translated src=- shape=b393419e vocab=f2b63833
-/
theorem tendsto_movingK_div_R_half :
    Tendsto (fun x ↦ movingK x / movingR x) atTop (nhds (1 / 2 : ℝ)) := by
  have hnonzero : ∀ᶠ x in atTop, (1 / 2 : ℝ) * movingR x ≠ 0 := by
    filter_upwards [eventually_moving_core_positive] with x hcore
    exact mul_ne_zero (by norm_num) hcore.2.2.2.1.ne'
  have hratio : Tendsto
      (fun x ↦ movingK x / ((1 / 2 : ℝ) * movingR x))
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hnonzero).mp movingK_isEquivalent_half_R
  have hscaled := hratio.const_mul (1 / 2 : ℝ)
  have ht : Tendsto (fun x ↦ movingK x / movingR x) atTop
      (nhds ((1 / 2 : ℝ) * 1)) := by
    apply hscaled.congr'
    filter_upwards [eventually_moving_core_positive] with x hcore
    field_simp [hcore.2.2.2.1.ne']
  simpa using ht

/-! ### The rounding scale in (10.24)--(10.25) -/

/-- The normalization `ηR`.-/
def movingEtaR (x : ℝ) : ℝ := movingEta x * movingR x

/-- The nonnegative floor loss `K₀-K`.-/
def movingFloorError (x : ℝ) : ℝ := movingK0 x - movingK x

/--
@isnad1 id=islittle.0h0v.s4.6f719b07a786 from=translated src=- shape=e1142068 vocab=6917e9de
-/
theorem scaleA_mul_sqrt_isLittleO_log2 :
    (fun x ↦ scaleA x * Real.sqrt (scaleA x)) =o[atTop] log2 := by
  have hlogBase :=
    (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).comp_tendsto
      tendsto_log2_atTop
  have hlog3 : log3 =o[atTop] (fun x ↦ Real.sqrt (log2 x)) := by
    apply hlogBase.congr'
    · filter_upwards [] with x
      rfl
    · filter_upwards [] with x
      simp [Function.comp_apply, Real.sqrt_eq_rpow]
  have hAhalf : scaleA =o[atTop] (fun x ↦ Real.sqrt (log2 x)) :=
    scaleA_isEquivalent_log3.isBigO.trans_isLittleO hlog3
  have hsqrtBig :
      (fun x ↦ Real.sqrt (scaleA x)) =O[atTop]
        (fun x ↦ Real.sqrt (log2 x)) :=
    scaleA_isLittleO_log2.isBigO.sqrt (eventually_log2_pos.mono fun x hx ↦ hx.le)
  have hprod := hAhalf.mul_isBigO hsqrtBig
  apply hprod.congr'
  · exact EventuallyEq.rfl
  · filter_upwards [eventually_log2_pos] with x hL2
    exact Real.mul_self_sqrt hL2.le

/--
@isnad1 id=eq.3h1v.s6.d79f5b542ffd from=translated src=- shape=f77c7e4d vocab=3d483a0c
-/
theorem movingTMain_div_etaR_eq {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) (hA : 0 < scaleA x) :
    movingTMain x / movingEtaR x =
      scaleA x * Real.sqrt (scaleA x) / log2 x := by
  have hs : Real.sqrt (scaleL x / log2 x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (div_pos hL hL2))
  have hAroot : Real.sqrt (scaleA x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hA)
  have hR : movingR x ≠ 0 := (movingR_pos hL hL2).ne'
  have hRrelation := movingR_div_sqrt_div_eq_log2 hL hL2
  unfold movingTMain movingEtaR movingEta
  field_simp [hs, hAroot, hR, hL2.ne'] at hRrelation ⊢
  nlinarith

/--
@isnad1 id=islittle.0h0v.s3.9972dfee2db3 from=translated src=- shape=47806ae7 vocab=32d9cda4
-/
theorem movingTMain_isLittleO_etaR : movingTMain =o[atTop] movingEtaR := by
  have hzero : Tendsto
      (fun x ↦ scaleA x * Real.sqrt (scaleA x) / log2 x)
      atTop (nhds 0) := scaleA_mul_sqrt_isLittleO_log2.tendsto_div_nhds_zero
  have hratio : Tendsto (fun x ↦ movingTMain x / movingEtaR x)
      atTop (nhds 0) := by
    apply hzero.congr'
    filter_upwards [eventually_moving_core_positive] with x hcore
    exact (movingTMain_div_etaR_eq hcore.1 hcore.2.1 hcore.2.2.1).symm
  refine isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_moving_core_positive] with x hcore
  intro hzero
  have hpos : 0 < movingEtaR x := by
    exact mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1
  exact (hpos.ne' hzero).elim

/-- The first estimate in (10.25): `T = o(ηR)`.
@isnad1 id=islittle.0h0v.s3.442b2fa4b69e from=translated src=- shape=47806ae7 vocab=32f54ce6
-/
theorem movingT_isLittleO_etaR : movingT =o[atTop] movingEtaR :=
  movingT_isEquivalent_main.isBigO.trans_isLittleO movingTMain_isLittleO_etaR

/--
@isnad1 id=tendsto.0h0v.s5.d2cf2e71ea53 from=translated src=- shape=93a4dec3 vocab=26c5b61c
-/
theorem tendsto_movingT_div_etaR_zero :
    Tendsto (fun x ↦ movingT x / movingEtaR x) atTop (nhds 0) :=
  movingT_isLittleO_etaR.tendsto_div_nhds_zero

/-- The actual paper-strength floor statement: `K = (1/2 - 2η)R + o(ηR)`.
@isnad1 id=islittle.0h0v.s3.24ad34c74c57 from=translated src=- shape=47806ae7 vocab=cc936337
-/
theorem movingFloorError_isLittleO_etaR : movingFloorError =o[atTop] movingEtaR := by
  have hratio : Tendsto (fun x ↦ movingFloorError x / movingEtaR x)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_moving_core_positive] with x hcore
      have herr := movingK_floor_error hcore.2.2.2.2.2.2.2 hcore.2.2.2.2.2.2.1.le
      have hden : 0 ≤ movingEtaR x :=
        (mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1).le
      exact div_nonneg herr.1 hden
    · filter_upwards [eventually_moving_core_positive] with x hcore
      have herr := movingK_floor_error hcore.2.2.2.2.2.2.2 hcore.2.2.2.2.2.2.1.le
      have hden : 0 ≤ movingEtaR x :=
        (mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1).le
      exact div_le_div_of_nonneg_right herr.2.le hden
    · exact tendsto_movingT_div_etaR_zero
  refine isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_moving_core_positive] with x hcore
  intro hzero
  have hpos : 0 < movingEtaR x := by
    exact mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1
  exact (hpos.ne' hzero).elim

/-! ### The remaining two normalizations in (10.25) -/

/-- Any fixed displayed logarithmic cube is negligible compared with `sqrt L`.
@isnad1 id=islittle.0h0v.s5.66cef6a4f637 from=translated src=- shape=87dd7a6b vocab=19e95023
-/
theorem log2_cube_isLittleO_sqrt_scaleL :
    (fun x ↦ log2 x ^ 3) =o[atTop] (fun x ↦ Real.sqrt (scaleL x)) := by
  have hbase :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_scaleL_atTop
  apply hbase.congr'
  · filter_upwards [eventually_scaleL_pos] with x hL
    simp [Function.comp_apply, log2, scaleL]
  · filter_upwards [eventually_scaleL_pos] with x hL
    simp [Function.comp_apply, Real.sqrt_eq_rpow]

/--
@isnad1 id=islittle.0h0v.s5.e43fb9ad73bf from=translated src=- shape=87dd7a6b vocab=19e95023
-/
theorem log2_sq_isLittleO_sqrt_scaleL :
    (fun x ↦ log2 x ^ 2) =o[atTop] (fun x ↦ Real.sqrt (scaleL x)) := by
  have hbase :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_scaleL_atTop
  apply hbase.congr'
  · filter_upwards [eventually_scaleL_pos] with x hL
    simp [Function.comp_apply, log2, scaleL]
  · filter_upwards [eventually_scaleL_pos] with x hL
    simp [Function.comp_apply, Real.sqrt_eq_rpow]

/--
@isnad1 id=eventual.0h0v.s3.0110f1b8d37d from=translated src=- shape=fae4e14a vocab=8569c540
-/
theorem eventually_scaleA_le_log2 : ∀ᶠ x in atTop, scaleA x ≤ log2 x := by
  have hbound := scaleA_isLittleO_log2.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_scaleA_pos, eventually_log2_pos] with x h hA hL2
  change |scaleA x| ≤ 1 * |log2 x| at h
  rw [abs_of_pos hA, abs_of_pos hL2, one_mul] at h
  exact h

/--
@isnad1 id=isbigo.0h0v.s3.05819d9184a6 from=translated src=- shape=47806ae7 vocab=1a7a04ba
-/
theorem movingJMain_isBigO_log2 : movingJMain =O[atTop] log2 := by
  apply IsBigO.of_bound 1
  filter_upwards [tendsto_scaleA_atTop.eventually_ge_atTop 1,
      eventually_log2_pos] with x hA hL2
  have hnonneg : 0 ≤ movingJMain x := by
    unfold movingJMain
    positivity
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hL2.le, one_mul]
  unfold movingJMain
  have hdiv : log2 x / scaleA x ≤ log2 x := by
    exact div_le_self hL2.le hA
  nlinarith

/--
@isnad1 id=isbigo.0h0v.s4.7e521c447a30 from=translated src=- shape=9aae1533 vocab=957f6302
-/
theorem movingJ_cast_isBigO_log2 :
    (fun x ↦ (movingJ x : ℝ)) =O[atTop] log2 :=
  movingJ_isEquivalent_main.isBigO.trans movingJMain_isBigO_log2

/--
@isnad1 id=isbigo.0h0v.s5.97d12da55cae from=translated src=- shape=4c7a98e6 vocab=c1d31efe
-/
theorem movingJ_sq_mul_log2_isBigO_cube :
    (fun x ↦ (movingJ x : ℝ) ^ 2 * log2 x) =O[atTop]
      (fun x ↦ log2 x ^ 3) := by
  have hsquare := movingJ_cast_isBigO_log2.mul movingJ_cast_isBigO_log2
  have hcube := hsquare.mul (isBigO_refl log2 atTop)
  calc
    (fun x ↦ (movingJ x : ℝ) ^ 2 * log2 x) =ᶠ[atTop]
        (fun x ↦ ((movingJ x : ℝ) * (movingJ x : ℝ)) * log2 x) := by
      filter_upwards [] with x
      rw [pow_two]
    _ =O[atTop] (fun x ↦ (log2 x * log2 x) * log2 x) := hcube
    _ =ᶠ[atTop] (fun x ↦ log2 x ^ 3) := by
      filter_upwards [] with x
      ring

/--
@isnad1 id=isbigo.0h0v.s3.94065d18f036 from=translated src=- shape=afbd0cda vocab=6903b192
-/
theorem sqrt_scaleL_isBigO_etaR :
    (fun x ↦ Real.sqrt (scaleL x)) =O[atTop] movingEtaR := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_moving_core_positive, eventually_scaleA_le_log2] with
      x hcore hAL2
  have hsqrtA : Real.sqrt (scaleA x) ≤ Real.sqrt (log2 x) :=
    Real.sqrt_le_sqrt hAL2
  have hsqrtL : 0 < Real.sqrt (scaleL x) := Real.sqrt_pos.2 hcore.1
  have hsqrtL2 : 0 < Real.sqrt (log2 x) := Real.sqrt_pos.2 hcore.2.1
  have hsqrtApos : 0 < Real.sqrt (scaleA x) := Real.sqrt_pos.2 hcore.2.2.1
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), one_mul]
  have htarget : Real.sqrt (scaleL x) ≤ movingEtaR x := by
    unfold movingEtaR movingEta movingR
    rw [Real.sqrt_mul hcore.1.le]
    calc
      Real.sqrt (scaleL x) ≤
          (Real.sqrt (scaleL x) * Real.sqrt (log2 x)) /
            Real.sqrt (scaleA x) := by
        apply (le_div_iff₀ hsqrtApos).mpr
        exact mul_le_mul_of_nonneg_left hsqrtA (Real.sqrt_nonneg _)
      _ = (Real.sqrt (scaleA x))⁻¹ *
          (Real.sqrt (scaleL x) * Real.sqrt (log2 x)) := by
        rw [div_eq_inv_mul]
  exact htarget.trans (le_abs_self _)

/-- The second estimate in (10.25): `J²L₂ = o(ηR)`.
@isnad1 id=islittle.0h0v.s5.7516985237a5 from=translated src=- shape=d444764d vocab=874cbe86
-/
theorem movingJ_sq_mul_log2_isLittleO_etaR :
    (fun x ↦ (movingJ x : ℝ) ^ 2 * log2 x) =o[atTop] movingEtaR :=
  movingJ_sq_mul_log2_isBigO_cube.trans_isLittleO
    (log2_cube_isLittleO_sqrt_scaleL.trans_isBigO sqrt_scaleL_isBigO_etaR)

/-- The normalization `ηL`.-/
def movingEtaL (x : ℝ) : ℝ := movingEta x * scaleL x

/--
@isnad1 id=eq.2h1v.s6.6a9b0401ed31 from=translated src=- shape=110d5522 vocab=530277d2
-/
theorem log2_mul_movingR_div_intermediate_eq {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) :
    (log2 x * movingR x) /
        (scaleL x / Real.sqrt (log2 x)) =
      log2 x ^ 2 / Real.sqrt (scaleL x) := by
  have hsqrtL : Real.sqrt (scaleL x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have hsqrtL2 : Real.sqrt (log2 x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL2)
  unfold movingR
  rw [Real.sqrt_mul hL.le]
  field_simp [hsqrtL, hsqrtL2, hL.ne', hL2.ne',
    Real.mul_self_sqrt hL.le, Real.mul_self_sqrt hL2.le]
  rw [Real.sq_sqrt hL.le, Real.sq_sqrt hL2.le]
  ring

/--
@isnad1 id=islittle.0h0v.s5.0697a99d2661 from=translated src=- shape=30ac79e0 vocab=904ecfbe
-/
theorem log2_mul_movingR_isLittleO_intermediate :
    (fun x ↦ log2 x * movingR x) =o[atTop]
      (fun x ↦ scaleL x / Real.sqrt (log2 x)) := by
  have hzero : Tendsto (fun x ↦ log2 x ^ 2 / Real.sqrt (scaleL x))
      atTop (nhds 0) := log2_sq_isLittleO_sqrt_scaleL.tendsto_div_nhds_zero
  have hratio : Tendsto
      (fun x ↦ (log2 x * movingR x) /
        (scaleL x / Real.sqrt (log2 x))) atTop (nhds 0) := by
    apply hzero.congr'
    filter_upwards [eventually_scaleL_pos, eventually_log2_pos] with x hL hL2
    exact (log2_mul_movingR_div_intermediate_eq hL hL2).symm
  refine isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_scaleL_pos, eventually_log2_pos] with x hL hL2
  intro hzero
  have hpos : 0 < scaleL x / Real.sqrt (log2 x) :=
    div_pos hL (Real.sqrt_pos.2 hL2)
  exact (hpos.ne' hzero).elim

/--
@isnad1 id=isbigo.0h0v.s4.d1f6f6779f86 from=translated src=- shape=3116060c vocab=af3b4757
-/
theorem intermediate_isBigO_etaL :
    (fun x ↦ scaleL x / Real.sqrt (log2 x)) =O[atTop] movingEtaL := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_moving_core_positive, eventually_scaleA_le_log2] with
      x hcore hAL2
  have hsqrtA : Real.sqrt (scaleA x) ≤ Real.sqrt (log2 x) :=
    Real.sqrt_le_sqrt hAL2
  have hsqrtApos : 0 < Real.sqrt (scaleA x) := Real.sqrt_pos.2 hcore.2.2.1
  have hsqrtL2pos : 0 < Real.sqrt (log2 x) := Real.sqrt_pos.2 hcore.2.1
  have hleft : 0 ≤ scaleL x / Real.sqrt (log2 x) :=
    (div_pos hcore.1 hsqrtL2pos).le
  rw [Real.norm_of_nonneg hleft, one_mul]
  have htarget : scaleL x / Real.sqrt (log2 x) ≤ movingEtaL x := by
    unfold movingEtaL movingEta
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hcore.1.le hsqrtApos hsqrtA
  exact htarget.trans (le_abs_self _)

/--
@isnad1 id=isbigo.0h0v.s3.9e0182aec0b2 from=translated src=- shape=47806ae7 vocab=d88f4ec3
-/
theorem movingK_isBigO_movingR : movingK =O[atTop] movingR :=
  movingK_isEquivalent_half_R.isBigO.trans
    (isBigO_const_mul_self (1 / 2 : ℝ) movingR atTop)

/--
@isnad1 id=isbigo.0h0v.s5.e6eeaf4515ad from=translated src=- shape=d7c2fdac vocab=495f251a
-/
theorem movingJ_mul_K_isBigO_log2_mul_R :
    (fun x ↦ (movingJ x : ℝ) * movingK x) =O[atTop]
      (fun x ↦ log2 x * movingR x) :=
  movingJ_cast_isBigO_log2.mul movingK_isBigO_movingR

/-- The final estimate in (10.25): `JK = o(ηL)`.
@isnad1 id=islittle.0h0v.s4.23d21ab430d9 from=translated src=- shape=eb1b0775 vocab=0956a17d
-/
theorem movingJ_mul_K_isLittleO_etaL :
    (fun x ↦ (movingJ x : ℝ) * movingK x) =o[atTop] movingEtaL :=
  movingJ_mul_K_isBigO_log2_mul_R.trans_isLittleO
    (log2_mul_movingR_isLittleO_intermediate.trans_isBigO intermediate_isBigO_etaL)

/--
@isnad1 id=islittle.0h0v.s3.6c8c2600349e from=translated src=- shape=47806ae7 vocab=6a823772
-/
theorem movingEtaL_isLittleO_scaleL : movingEtaL =o[atTop] scaleL := by
  have hratio : Tendsto (fun x ↦ movingEtaL x / scaleL x) atTop (nhds 0) := by
    apply tendsto_movingEta_zero.congr'
    filter_upwards [eventually_scaleL_pos] with x hL
    unfold movingEtaL
    field_simp [hL.ne']
  refine isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_scaleL_pos] with x hL
  exact fun hzero ↦ (hL.ne' hzero).elim

/--
@isnad1 id=islittle.0h0v.s4.5ab267a3ee1d from=translated src=- shape=eb1b0775 vocab=0dcfd578
-/
theorem movingJ_mul_K_isLittleO_scaleL :
    (fun x ↦ (movingJ x : ℝ) * movingK x) =o[atTop] scaleL :=
  movingJ_mul_K_isLittleO_etaL.trans movingEtaL_isLittleO_scaleL

/--
@isnad1 id=isbigo.0h0v.s3.2bef920c1073 from=translated src=- shape=afbd0cda vocab=802d5c35
-/
theorem sqrt_scaleL_isBigO_scaleL :
    (fun x ↦ Real.sqrt (scaleL x)) =O[atTop] scaleL := by
  apply IsBigO.of_bound 1
  filter_upwards [tendsto_scaleL_atTop.eventually_ge_atTop 1] with x hL
  have hLnonneg : 0 ≤ scaleL x := zero_le_one.trans hL
  have hsqrt : Real.sqrt (scaleL x) ≤ scaleL x :=
    (Real.sqrt_le_self_iff).2 (Or.inr hL)
  change |Real.sqrt (scaleL x)| ≤ 1 * |scaleL x|
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hLnonneg, one_mul]
  exact hsqrt

/--
@isnad1 id=islittle.0h0v.s4.95c85959c3b4 from=translated src=- shape=eb1b0775 vocab=297d9efc
-/
theorem movingJ_mul_log2_isLittleO_scaleL :
    (fun x ↦ (movingJ x : ℝ) * log2 x) =o[atTop] scaleL := by
  have hbig : (fun x ↦ (movingJ x : ℝ) * log2 x) =O[atTop]
      (fun x ↦ log2 x ^ 2) := by
    have h := movingJ_cast_isBigO_log2.mul (isBigO_refl log2 atTop)
    apply h.congr_right
    intro x
    rw [pow_two]
  exact hbig.trans_isLittleO
    (log2_sq_isLittleO_sqrt_scaleL.trans_isBigO sqrt_scaleL_isBigO_scaleL)

/-! ## Source and transfer thresholds from Lemmas 10.16 and 10.18 -/

/-- The logarithm of `H_src = 2⁻ʲ x¹⁄² Z⁻²ʲ`.-/
def movingSourceLogThreshold (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * scaleL x -
    2 * (movingJ x : ℝ) * movingK x -
    (movingJ x : ℝ) * Real.log 2

/-- The positive source threshold `H_src`.-/
def movingHsrc (x : ℝ) : ℝ := Real.exp (movingSourceLogThreshold x)

/-- `v_src = log H_src / K`.-/
def movingVsrc (x : ℝ) : ℝ := Real.log (movingHsrc x) / movingK x

/-- Lower transfer parameter `u_tr^-`.-/
def movingUtrMinus (x : ℝ) : ℝ :=
  (scaleL x - 3 * movingK x + Real.log 2) / (2 * movingK x)

/-- Upper transfer parameter `u_tr^+`.-/
def movingUtrPlus (x : ℝ) : ℝ :=
  (scaleL x - movingK x + Real.log 2) / movingK x

/--
@isnad1 id=lt.0h1v.s3.6c64b9037c1d from=translated src=- shape=8a62b088 vocab=8b3f5f04
-/
theorem movingHsrc_pos (x : ℝ) : 0 < movingHsrc x := Real.exp_pos _

/--
@isnad1 id=eq.0h1v.s3.45a9cbfe9fd6 from=translated src=- shape=c52356c6 vocab=9c617592
-/
@[simp] theorem log_movingHsrc (x : ℝ) :
    Real.log (movingHsrc x) = movingSourceLogThreshold x := by
  rw [movingHsrc, Real.log_exp]

/--
@isnad1 id=eq.0h1v.s4.abd20cc2d083 from=translated src=- shape=f108d266 vocab=bb241b7a
-/
@[simp] theorem movingVsrc_eq_sourceLog_div (x : ℝ) :
    movingVsrc x = movingSourceLogThreshold x / movingK x := by
  rw [movingVsrc, log_movingHsrc]

/--
@isnad1 id=isequiva.0h0v.s5.26c6b243532f from=translated src=- shape=d9db04d6 vocab=3c7eab68
-/
theorem movingSourceLogThreshold_isEquivalent_half_L :
    movingSourceLogThreshold ~[atTop] (fun x ↦ (1 / 2 : ℝ) * scaleL x) := by
  have hJK : Tendsto
      (fun x ↦ ((movingJ x : ℝ) * movingK x) / scaleL x)
      atTop (nhds 0) := movingJ_mul_K_isLittleO_scaleL.tendsto_div_nhds_zero
  have hJconst : Tendsto
      (fun x ↦ ((movingJ x : ℝ) * Real.log 2) / scaleL x)
      atTop (nhds 0) := by
    have hbig : (fun x ↦ (movingJ x : ℝ) * Real.log 2) =O[atTop] log2 := by
      have h := movingJ_cast_isBigO_log2.const_mul_left (Real.log 2)
      apply h.congr_left
      intro x
      ring
    exact (hbig.trans_isLittleO log2_isLittleO_scaleL).tendsto_div_nhds_zero
  apply isEquivalent_of_tendsto_one
  have hlimit : Tendsto
      (fun x ↦ (1 : ℝ) -
        (4 * (((movingJ x : ℝ) * movingK x) / scaleL x) +
          2 * (((movingJ x : ℝ) * Real.log 2) / scaleL x)))
      atTop (nhds 1) := by
    convert tendsto_const_nhds.sub
      ((hJK.const_mul 4).add (hJconst.const_mul 2)) using 1
    all_goals norm_num
  apply hlimit.congr'
  filter_upwards [eventually_scaleL_pos] with x hL
  change 1 -
      (4 * (((movingJ x : ℝ) * movingK x) / scaleL x) +
        2 * (((movingJ x : ℝ) * Real.log 2) / scaleL x)) =
    movingSourceLogThreshold x / ((1 / 2 : ℝ) * scaleL x)
  unfold movingSourceLogThreshold
  field_simp [hL.ne']
  ring

/--
@isnad1 id=tendsto.0h0v.s3.e218be8f8558 from=translated src=- shape=41b74a9e vocab=8d3273b1
-/
theorem tendsto_movingSourceLogThreshold_atTop :
    Tendsto movingSourceLogThreshold atTop atTop := by
  have hhalf : Tendsto (fun x ↦ (1 / 2 : ℝ) * scaleL x) atTop atTop :=
    tendsto_scaleL_atTop.const_mul_atTop (by norm_num)
  exact movingSourceLogThreshold_isEquivalent_half_L.symm.tendsto_atTop hhalf

/--
@isnad1 id=tendsto.0h0v.s3.d8bcc7c11ccb from=translated src=- shape=41b74a9e vocab=15a08514
-/
theorem tendsto_movingHsrc_atTop : Tendsto movingHsrc atTop atTop :=
  Real.tendsto_exp_atTop.comp tendsto_movingSourceLogThreshold_atTop

/--
@isnad1 id=eventual.0h0v.s4.77ba41bb36a7 from=translated src=- shape=012bd729 vocab=610013d7
-/
theorem eventually_three_lt_movingHsrc : ∀ᶠ x in atTop, 3 < movingHsrc x :=
  tendsto_movingHsrc_atTop.eventually_gt_atTop 3

/--
@isnad1 id=isequiva.0h0v.s5.92c19b762dcb from=translated src=- shape=7d742454 vocab=fd460c64
-/
theorem movingVsrc_isEquivalent_sqrt_ratio :
    movingVsrc ~[atTop] (fun x ↦ Real.sqrt (scaleL x / log2 x)) := by
  have hquot := movingSourceLogThreshold_isEquivalent_half_L.div
    movingK_isEquivalent_half_R
  have hleft : (movingSourceLogThreshold / movingK) =ᶠ[atTop] movingVsrc := by
    filter_upwards [] with x
    exact (movingVsrc_eq_sourceLog_div x).symm
  have hright :
      ((fun x ↦ (1 / 2 : ℝ) * scaleL x) /
        (fun x ↦ (1 / 2 : ℝ) * movingR x)) =ᶠ[atTop]
        (fun x ↦ Real.sqrt (scaleL x / log2 x)) := by
    filter_upwards [eventually_moving_core_positive] with x hcore
    change ((1 / 2 : ℝ) * scaleL x) / ((1 / 2 : ℝ) * movingR x) =
      Real.sqrt (scaleL x / log2 x)
    rw [← scaleL_div_movingR_eq_sqrt_div hcore.1 hcore.2.1]
    field_simp [hcore.2.2.2.1.ne']
  exact (hquot.congr_left hleft).congr_right hright

/--
@isnad1 id=tendsto.0h0v.s3.78f7a0ab8592 from=translated src=- shape=41b74a9e vocab=745a0441
-/
theorem tendsto_movingVsrc_atTop : Tendsto movingVsrc atTop atTop :=
  movingVsrc_isEquivalent_sqrt_ratio.symm.tendsto_atTop
    tendsto_sqrt_scaleL_div_log2_atTop

/--
@isnad1 id=eventual.0h0v.s4.d8c117681061 from=translated src=- shape=012bd729 vocab=8e2befc1
-/
theorem eventually_three_le_movingVsrc : ∀ᶠ x in atTop, 3 ≤ movingVsrc x :=
  tendsto_movingVsrc_atTop.eventually_ge_atTop 3

private theorem movingK_isLittleO_scaleL_for_transfer : movingK =o[atTop] scaleL := by
  have hInv : Tendsto
      (fun x ↦ (Real.sqrt (scaleL x / log2 x))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_scaleL_div_log2_atTop
  have hRratio : Tendsto (fun x ↦ movingR x / scaleL x) atTop (nhds 0) := by
    apply hInv.congr'
    filter_upwards [eventually_scaleL_pos, eventually_log2_pos] with x hL hL2
    rw [← scaleL_div_movingR_eq_sqrt_div hL hL2]
    rw [inv_div]
  have hRlittle : movingR =o[atTop] scaleL := by
    refine isLittleO_of_tendsto' ?_ hRratio
    filter_upwards [eventually_scaleL_pos] with x hL
    exact fun hzero ↦ (hL.ne' hzero).elim
  exact movingK_isEquivalent_half_R.isBigO.trans_isLittleO
    (hRlittle.const_mul_left (1 / 2 : ℝ))

/--
@isnad1 id=tendsto.0h0v.s4.3cb67372d41d from=translated src=- shape=53861ef7 vocab=4dd20d3c
-/
theorem tendsto_scaleL_div_movingK_atTop :
    Tendsto (fun x ↦ scaleL x / movingK x) atTop atTop := by
  have hzero : Tendsto (fun x ↦ movingK x / scaleL x) atTop (nhds 0) :=
    movingK_isLittleO_scaleL_for_transfer.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x in atTop, 0 < movingK x / scaleL x := by
    filter_upwards [tendsto_movingK_atTop.eventually_gt_atTop 0,
      eventually_scaleL_pos] with x hK hL
    exact div_pos hK hL
  have hwithin : Tendsto (fun x ↦ movingK x / scaleL x) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [tendsto_movingK_atTop.eventually_gt_atTop 0,
      eventually_scaleL_pos] with x hK hL
  change (movingK x / scaleL x)⁻¹ = scaleL x / movingK x
  rw [inv_div]

/--
@isnad1 id=tendsto.0h0v.s5.24c228043720 from=translated src=- shape=cc85db5c vocab=5f61b577
-/
theorem tendsto_log_two_div_movingK_zero :
    Tendsto (fun x ↦ Real.log 2 / movingK x) atTop (nhds 0) := by
  have hinv : Tendsto (fun x ↦ (movingK x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_movingK_atTop
  simpa [div_eq_mul_inv] using hinv.const_mul (Real.log 2)

/--
@isnad1 id=tendsto.0h0v.s3.a027ad1052af from=translated src=- shape=41b74a9e vocab=7411c60c
-/
theorem tendsto_movingUtrMinus_atTop : Tendsto movingUtrMinus atTop atTop := by
  have hrest : Tendsto (fun x ↦ (-3 : ℝ) + Real.log 2 / movingK x)
      atTop (nhds (-3)) := by
    simpa using tendsto_const_nhds.add tendsto_log_two_div_movingK_zero
  have hsum := tendsto_scaleL_div_movingK_atTop.atTop_add hrest
  have hhalf := hsum.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  apply hhalf.congr'
  filter_upwards [tendsto_movingK_atTop.eventually_gt_atTop 0] with x hK
  unfold movingUtrMinus
  field_simp [hK.ne']
  ring

/--
@isnad1 id=tendsto.0h0v.s3.108dd11c7572 from=translated src=- shape=41b74a9e vocab=125d4179
-/
theorem tendsto_movingUtrPlus_atTop : Tendsto movingUtrPlus atTop atTop := by
  have hrest : Tendsto (fun x ↦ (-1 : ℝ) + Real.log 2 / movingK x)
      atTop (nhds (-1)) := by
    simpa using tendsto_const_nhds.add tendsto_log_two_div_movingK_zero
  have hsum := tendsto_scaleL_div_movingK_atTop.atTop_add hrest
  apply hsum.congr'
  filter_upwards [tendsto_movingK_atTop.eventually_gt_atTop 0] with x hK
  unfold movingUtrPlus
  field_simp [hK.ne']
  ring

/--
@isnad1 id=eventual.0h1v.s3.a582b20a7a28 from=translated src=- shape=e66203b3 vocab=738693b4
-/
theorem eventually_lower_transfer_admissible (u0 : ℝ) :
    ∀ᶠ x in atTop, u0 ≤ movingUtrMinus x :=
  tendsto_movingUtrMinus_atTop.eventually_ge_atTop u0

/--
@isnad1 id=eventual.0h0v.s4.8e2f215b4f04 from=translated src=- shape=012bd729 vocab=a1adb076
-/
theorem eventually_upper_transfer_ge_three :
    ∀ᶠ x in atTop, 3 ≤ movingUtrPlus x :=
  tendsto_movingUtrPlus_atTop.eventually_ge_atTop 3

/-! ## Proposition 10.17 and Lemma 10.18: named error expressions -/

/-- The transfer error displayed in (10.33).-/
def movingTransferError (C : ℝ) (x : ℝ) : ℝ :=
  C / movingEtaR x *
    (log2 x + log2 (3 * movingZ x ^ 2) +
      movingUtrPlus x / Real.log (movingUtrPlus x))

/-- The two second-order margin inequalities in (10.34).-/
def HasMovingSaddleMargins (x : ℝ) : Prop :=
  movingVsrc x * Real.log (movingVsrc x) ≥ movingK x + 3 * movingEtaR x ∧
  movingUtrMinus x * Real.log (movingUtrMinus x) ≥
    movingK x + 3 * movingEtaR x

/-- The `L₂/(ηR)` component of the transfer error vanishes unconditionally.
@isnad1 id=islittle.0h0v.s3.821e6f81470b from=translated src=- shape=47806ae7 vocab=8d10d62f
-/
theorem log2_isLittleO_etaR : log2 =o[atTop] movingEtaR := by
  have hbase :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_scaleL_atTop
  have hlog : log2 =o[atTop] (fun x ↦ Real.sqrt (scaleL x)) := by
    apply hbase.congr'
    · filter_upwards [eventually_scaleL_pos] with x hL
      simp [Function.comp_apply, log2, scaleL]
    · filter_upwards [eventually_scaleL_pos] with x hL
      simp [Function.comp_apply, Real.sqrt_eq_rpow]
  exact hlog.trans_isBigO sqrt_scaleL_isBigO_etaR

/-- Once the two genuinely analytic terms in (10.33) are supplied, the named transfer error tends to zero.
@isnad1 id=tendsto.2h1v.s7.30d9f4518eb5 from=translated src=- shape=d876c6b4 vocab=36cdb6c3
-/
theorem movingTransferError_tendsto_zero
    {C : ℝ}
    (hlogZ : Tendsto (fun x ↦ log2 (3 * movingZ x ^ 2) / movingEtaR x)
      atTop (nhds 0))
    (hu : Tendsto (fun x ↦
      (movingUtrPlus x / Real.log (movingUtrPlus x)) / movingEtaR x)
      atTop (nhds 0)) :
    Tendsto (movingTransferError C) atTop (nhds 0) := by
  have hL2 : Tendsto (fun x ↦ log2 x / movingEtaR x) atTop (nhds 0) :=
    log2_isLittleO_etaR.tendsto_div_nhds_zero
  have hsum := (hL2.add hlogZ).add hu
  have hscaled := hsum.const_mul C
  have ht : Tendsto (movingTransferError C) atTop
      (nhds (C * (0 + 0 + 0))) := by
    apply hscaled.congr'
    filter_upwards [eventually_moving_core_positive] with x hcore
    unfold movingTransferError
    have hden : movingEtaR x ≠ 0 :=
      (mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1).ne'
    field_simp [hden]
  simpa using ht

/-- A faithful parameterized version of the dependency ledger (10.32).-/
def movingDependencyError
    (C : ℝ) (logBell logBlockMass : ℝ → ℝ) (x : ℝ) : ℝ :=
  (movingT x + logBell x + (movingJ x : ℝ) * logBlockMass x +
      (movingJ x : ℝ) * Real.log (1 + scaleL x / movingT x)) / movingEtaR x +
  ((movingJ x : ℝ) ^ 2 +
      (movingJ x : ℝ) ^ 2 * log2 (3 * (movingJ x : ℝ)) +
      3 * (movingJ x : ℝ) *
        Real.log (C * (movingJ x : ℝ) *
          (1 + (movingJ x : ℝ) + scaleL x / movingT x)) +
      C * (movingJ x : ℝ) / movingY x) / movingEtaR x +
  (movingJ x : ℝ) / movingEtaR x *
      (log2 (3 * movingZ x) + movingVsrc x / Real.log (movingVsrc x)) +
  (movingJ x : ℝ) * movingK x / movingEtaL x

/-- Exact algebraic aggregation: if the four normalized ledger rows vanish, so does (10.32).
@isnad1 id=tendsto.3h3v.s8.95a3d235edff from=translated src=- shape=69c1ca37 vocab=da135449
-/
theorem movingDependencyError_tendsto_zero_of_groups
    {C : ℝ} {logBell logBlockMass : ℝ → ℝ}
    (h1 : Tendsto (fun x ↦
      (movingT x + logBell x + (movingJ x : ℝ) * logBlockMass x +
        (movingJ x : ℝ) * Real.log (1 + scaleL x / movingT x)) / movingEtaR x)
      atTop (nhds 0))
    (h2 : Tendsto (fun x ↦
      ((movingJ x : ℝ) ^ 2 +
        (movingJ x : ℝ) ^ 2 * log2 (3 * (movingJ x : ℝ)) +
        3 * (movingJ x : ℝ) *
          Real.log (C * (movingJ x : ℝ) *
            (1 + (movingJ x : ℝ) + scaleL x / movingT x)) +
        C * (movingJ x : ℝ) / movingY x) / movingEtaR x)
      atTop (nhds 0))
    (h3 : Tendsto (fun x ↦
      (movingJ x : ℝ) / movingEtaR x *
        (log2 (3 * movingZ x) + movingVsrc x / Real.log (movingVsrc x)))
      atTop (nhds 0)) :
    Tendsto (movingDependencyError C logBell logBlockMass) atTop (nhds 0) := by
  have h4 : Tendsto (fun x ↦
      (movingJ x : ℝ) * movingK x / movingEtaL x) atTop (nhds 0) :=
    movingJ_mul_K_isLittleO_etaL.tendsto_div_nhds_zero
  change Tendsto (fun x ↦
    (movingT x + logBell x + (movingJ x : ℝ) * logBlockMass x +
        (movingJ x : ℝ) * Real.log (1 + scaleL x / movingT x)) / movingEtaR x +
    ((movingJ x : ℝ) ^ 2 +
        (movingJ x : ℝ) ^ 2 * log2 (3 * (movingJ x : ℝ)) +
        3 * (movingJ x : ℝ) *
          Real.log (C * (movingJ x : ℝ) *
            (1 + (movingJ x : ℝ) + scaleL x / movingT x)) +
        C * (movingJ x : ℝ) / movingY x) / movingEtaR x +
    (movingJ x : ℝ) / movingEtaR x *
        (log2 (3 * movingZ x) + movingVsrc x / Real.log (movingVsrc x)) +
    (movingJ x : ℝ) * movingK x / movingEtaL x) atTop (nhds 0)
  simpa only [zero_add] using ((h1.add h2).add h3).add h4

/-! ## Lemma 10.16: eventual admissibility -/

/--
@isnad1 id=eq.2h1v.s5.4823cada1aa4 from=translated src=- shape=8aaf0cbe vocab=93516ab6
-/
theorem movingR_div_scaleL_eq_sqrt_div {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) :
    movingR x / scaleL x = Real.sqrt (log2 x / scaleL x) := by
  rw [movingR, Real.sqrt_mul hL.le]
  calc
    (Real.sqrt (scaleL x) * Real.sqrt (log2 x)) / scaleL x =
        (Real.sqrt (scaleL x) * Real.sqrt (log2 x)) /
          (Real.sqrt (scaleL x) * Real.sqrt (scaleL x)) := by
      rw [Real.mul_self_sqrt hL.le]
    _ = Real.sqrt (log2 x) / Real.sqrt (scaleL x) := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 hL), ne_of_gt (Real.sqrt_pos.2 hL2)]
    _ = Real.sqrt (log2 x / scaleL x) := by
      rw [Real.sqrt_div hL2.le]

/--
@isnad1 id=tendsto.0h0v.s5.5df6f8e2edf9 from=translated src=- shape=93a4dec3 vocab=069aa0bf
-/
theorem tendsto_movingR_div_scaleL_zero :
    Tendsto (fun x ↦ movingR x / scaleL x) atTop (nhds 0) := by
  have hratio : Tendsto (fun x ↦ log2 x / scaleL x) atTop (nhds 0) :=
    log2_isLittleO_scaleL.tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun x ↦ Real.sqrt (log2 x / scaleL x))
      atTop (nhds 0) := by
    simpa using hratio.sqrt
  apply hsqrt.congr'
  filter_upwards [eventually_scaleL_pos, eventually_log2_pos] with x hL hL2
  exact (movingR_div_scaleL_eq_sqrt_div hL hL2).symm

/--
@isnad1 id=islittle.0h0v.s3.c6172b80c3a1 from=translated src=- shape=47806ae7 vocab=0339a74b
-/
theorem movingR_isLittleO_scaleL : movingR =o[atTop] scaleL := by
  refine isLittleO_of_tendsto' ?_ tendsto_movingR_div_scaleL_zero
  filter_upwards [eventually_scaleL_pos] with x hL
  exact fun hzero ↦ (hL.ne' hzero).elim

/--
@isnad1 id=islittle.0h0v.s3.727ec49b47c9 from=translated src=- shape=47806ae7 vocab=9aff9d56
-/
theorem movingK_isLittleO_scaleL : movingK =o[atTop] scaleL :=
  movingK_isEquivalent_half_R.isBigO.trans_isLittleO
    (movingR_isLittleO_scaleL.const_mul_left (1 / 2 : ℝ))

/--
@isnad1 id=eventual.0h0v.s4.b5e3dbbd4381 from=translated src=- shape=012bd729 vocab=f5aa8b67
-/
theorem eventually_movingK_pos : ∀ᶠ x in atTop, 0 < movingK x := by
  filter_upwards [eventually_moving_core_positive, eventually_two_le_movingJ] with x hcore hJ
  unfold movingK
  exact mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt hJ)) hcore.2.2.2.2.2.2.2

/--
@isnad1 id=tendsto.0h0v.s3.e7b09c15eacf from=translated src=- shape=41b74a9e vocab=8554b683
-/
theorem tendsto_movingY_atTop : Tendsto movingY atTop atTop :=
  Real.tendsto_exp_atTop.comp tendsto_movingT_atTop

/--
@isnad1 id=tendsto.0h0v.s3.5226772f911f from=translated src=- shape=41b74a9e vocab=de557bcd
-/
theorem tendsto_movingZ_atTop : Tendsto movingZ atTop atTop :=
  Real.tendsto_exp_atTop.comp tendsto_movingK_atTop

/-- The eventual inequalities (10.29).-/
structure MovingAdmissibility (x : ℝ) : Prop where
  A_pos : 0 < scaleA x
  rank_ge_two : 2 ≤ movingJ x
  three_le_y : 3 ≤ movingY x
  y_lt_Z : movingY x < movingZ x
  Z_lt_x : movingZ x < x
  three_mul_Z_cube_lt_two_mul_x : 3 * movingZ x ^ 3 < 2 * x

/--
@isnad1 id=eventual.0h0v.s3.b2be8ab4551a from=translated src=- shape=07c3c963 vocab=986c14d8
-/
theorem eventually_movingAdmissibility :
    ∀ᶠ x in atTop, MovingAdmissibility x := by
  have hKsmall := movingK_isLittleO_scaleL.bound (by norm_num : (0 : ℝ) < 1 / 6)
  have hLlarge : ∀ᶠ x in atTop,
      Real.log 3 - Real.log 2 < (1 / 2 : ℝ) * scaleL x := by
    have ht := tendsto_scaleL_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    exact ht.eventually_gt_atTop (Real.log 3 - Real.log 2)
  have hTlarge : ∀ᶠ x in atTop, Real.log 3 ≤ movingT x :=
    tendsto_movingT_atTop.eventually_ge_atTop (Real.log 3)
  filter_upwards [eventually_moving_core_positive, eventually_two_le_movingJ,
      eventually_movingK_pos, hKsmall, hLlarge, hTlarge,
      (tendsto_id.eventually_gt_atTop (0 : ℝ))] with
      x hcore hJ hKpos hKsmall hLlarge hTlarge hx
  have hx' : 0 < x := by simpa using hx
  have hKbound : movingK x ≤ (1 / 6 : ℝ) * scaleL x := by
    have hT := hcore.2.2.2.2.2.2.2
    have hlog : 0 ≤ Real.log x := by simpa [scaleL] using hcore.1.le
    simpa [movingK, scaleL, Real.norm_of_nonneg hT.le,
      Real.norm_of_nonneg hlog] using hKsmall
  have hTK : movingT x < movingK x := by
    rw [movingK]
    have hT := hcore.2.2.2.2.2.2.2
    have hJreal : (2 : ℝ) ≤ movingJ x := by exact_mod_cast hJ
    nlinarith
  have hthreeY : 3 ≤ movingY x := by
    rw [movingY, ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hTlarge
  have hyZ : movingY x < movingZ x := by
    exact Real.exp_lt_exp.mpr hTK
  have hKltL : movingK x < scaleL x := by
    nlinarith
  have hZx : movingZ x < x := by
    calc
      movingZ x = Real.exp (movingK x) := rfl
      _ < Real.exp (scaleL x) := Real.exp_lt_exp.mpr hKltL
      _ = x := by rw [scaleL, Real.exp_log hx']
  have hlogCube : Real.log 3 + 3 * movingK x < Real.log 2 + scaleL x := by
    nlinarith
  have hcube : 3 * movingZ x ^ 3 < 2 * x := by
    calc
      3 * movingZ x ^ 3 = Real.exp (Real.log 3 + 3 * movingK x) := by
        rw [movingZ, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3),
          show (3 : ℝ) = (3 : ℕ) by norm_num]
        exact congrArg (fun z : ℝ ↦ 3 * z)
          (Real.exp_nat_mul (movingK x) 3).symm
      _ < Real.exp (Real.log 2 + scaleL x) := Real.exp_lt_exp.mpr hlogCube
      _ = 2 * x := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          scaleL, Real.exp_log hx']
  exact ⟨hcore.2.2.1, hJ, hthreeY, hyZ, hZx, hcube⟩

/-! ### The remaining inequalities in Lemma 10.16 -/

/-- Exact cancellation behind `sqrt(L/L₂) = o(R)`.
@isnad1 id=eq.2h1v.s6.ea1d3995ab56 from=translated src=- shape=ddf6f203 vocab=93516ab6
-/
theorem sqrt_scaleL_div_log2_div_movingR_eq {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) :
    Real.sqrt (scaleL x / log2 x) / movingR x = 1 / log2 x := by
  rw [← scaleL_div_movingR_eq_sqrt_div hL hL2]
  have hR := movingR_pos hL hL2
  have hRsq := movingR_sq hL.le hL2.le
  field_simp [hR.ne', hL.ne', hL2.ne'] at hRsq ⊢
  nlinarith

/--
@isnad1 id=islittle.0h0v.s4.d4d1801d3d7f from=translated src=- shape=1c93d0b4 vocab=35da5f3c
-/
theorem sqrt_scaleL_div_log2_isLittleO_movingR :
    (fun x ↦ Real.sqrt (scaleL x / log2 x)) =o[atTop] movingR := by
  have hzero : Tendsto (fun x ↦ 1 / log2 x) atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp tendsto_log2_atTop
    apply hinv.congr'
    filter_upwards [] with x
    simp [one_div]
  have hratio : Tendsto
      (fun x ↦ Real.sqrt (scaleL x / log2 x) / movingR x)
      atTop (nhds 0) := by
    apply hzero.congr'
    filter_upwards [eventually_scaleL_pos, eventually_log2_pos] with x hL hL2
    exact (sqrt_scaleL_div_log2_div_movingR_eq hL hL2).symm
  refine isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_moving_core_positive] with x hcore
  exact fun hzero ↦ (hcore.2.2.2.1.ne' hzero).elim

/--
@isnad1 id=isbigo.0h0v.s3.c98e17c80078 from=translated src=- shape=47806ae7 vocab=d88f4ec3
-/
theorem movingR_isBigO_movingK : movingR =O[atTop] movingK :=
  (isBigO_self_const_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) movingR atTop).trans
    movingK_isEquivalent_half_R.symm.isBigO

/--
@isnad1 id=islittle.0h0v.s3.0f5628025c49 from=translated src=- shape=47806ae7 vocab=2768e1a6
-/
theorem movingVsrc_isLittleO_movingK : movingVsrc =o[atTop] movingK :=
  movingVsrc_isEquivalent_sqrt_ratio.isBigO.trans_isLittleO
    (sqrt_scaleL_div_log2_isLittleO_movingR.trans_isBigO movingR_isBigO_movingK)

/-- The main quotient in `u⁺_tr` has the same order as `sqrt(L/L₂)`.
@isnad1 id=isbigo.0h0v.s5.116abd29bfa0 from=translated src=- shape=5cce1eb1 vocab=3841c5fc
-/
theorem scaleL_div_movingK_isBigO_sqrt_ratio :
    (fun x ↦ scaleL x / movingK x) =O[atTop]
      (fun x ↦ Real.sqrt (scaleL x / log2 x)) := by
  have hquot := (IsEquivalent.refl (u := scaleL) (l := atTop)).div
    movingK_isEquivalent_half_R
  have heq :
      ((fun x ↦ scaleL x) / (fun x ↦ (1 / 2 : ℝ) * movingR x)) =ᶠ[atTop]
        (fun x ↦ 2 * Real.sqrt (scaleL x / log2 x)) := by
    filter_upwards [eventually_scaleL_pos, eventually_log2_pos] with x hL hL2
    change scaleL x / ((1 / 2 : ℝ) * movingR x) =
      2 * Real.sqrt (scaleL x / log2 x)
    rw [← scaleL_div_movingR_eq_sqrt_div hL hL2]
    field_simp [movingR_pos hL hL2 |>.ne']
  exact (hquot.congr_right heq).isBigO.trans
    (isBigO_const_mul_self 2 (fun x ↦ Real.sqrt (scaleL x / log2 x)) atTop)

/--
@isnad1 id=isbigo.0h0v.s4.f4f92190dff8 from=translated src=- shape=8c35d723 vocab=cd42636c
-/
theorem movingUtrPlus_isBigO_scaleL_div_movingK :
    movingUtrPlus =O[atTop] (fun x ↦ scaleL x / movingK x) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_movingK_pos,
      tendsto_movingK_atTop.eventually_ge_atTop 1,
      tendsto_scaleL_div_movingK_atTop.eventually_ge_atTop 1] with x hK hKone hquot
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogdiv0 : 0 ≤ Real.log 2 / movingK x := div_nonneg hlog0 hK.le
  have hlogdiv1 : Real.log 2 / movingK x ≤ 1 := by
    exact (div_le_one hK).2 (hlog1.trans hKone)
  have heq : movingUtrPlus x =
      scaleL x / movingK x - 1 + Real.log 2 / movingK x := by
    unfold movingUtrPlus
    field_simp [hK.ne']
  have hu0 : 0 ≤ movingUtrPlus x := by rw [heq]; linarith
  have huq : movingUtrPlus x ≤ scaleL x / movingK x := by rw [heq]; linarith
  rw [Real.norm_of_nonneg hu0, Real.norm_of_nonneg (zero_le_one.trans hquot), one_mul]
  exact huq

/--
@isnad1 id=islittle.0h0v.s3.84622c8209af from=translated src=- shape=47806ae7 vocab=04cfff8b
-/
theorem movingUtrPlus_isLittleO_movingK : movingUtrPlus =o[atTop] movingK :=
  (movingUtrPlus_isBigO_scaleL_div_movingK.trans
      scaleL_div_movingK_isBigO_sqrt_ratio).trans_isLittleO
    (sqrt_scaleL_div_log2_isLittleO_movingR.trans_isBigO movingR_isBigO_movingK)

/--
@isnad1 id=islittle.0h0v.s3.ea7becec5346 from=translated src=- shape=afbd0cda vocab=55e0f774
-/
theorem log_movingVsrc_isLittleO_movingK :
    (fun x ↦ Real.log (movingVsrc x)) =o[atTop] movingK := by
  have hlog := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_movingVsrc_atTop
  have hlog' : (fun x ↦ Real.log (movingVsrc x)) =o[atTop] movingVsrc := by
    simpa [Function.comp_def] using hlog
  exact hlog'.trans movingVsrc_isLittleO_movingK

/--
@isnad1 id=islittle.0h0v.s3.a6d36c9422fd from=translated src=- shape=afbd0cda vocab=2f4a1a1c
-/
theorem log_movingUtrPlus_isLittleO_movingK :
    (fun x ↦ Real.log (movingUtrPlus x)) =o[atTop] movingK := by
  have hlog := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_movingUtrPlus_atTop
  have hlog' : (fun x ↦ Real.log (movingUtrPlus x)) =o[atTop] movingUtrPlus := by
    simpa [Function.comp_def] using hlog
  exact hlog'.trans movingUtrPlus_isLittleO_movingK

/-- The logarithmic part of (10.30).
@isnad1 id=eventual.0h0v.s5.d17dd03a8caa from=translated src=- shape=1e37f32d vocab=0b03d8e3
-/
theorem eventually_log_movingVsrc_le_half_K :
    ∀ᶠ x in atTop, Real.log (movingVsrc x) ≤ (1 / 2 : ℝ) * movingK x := by
  have hbound := log_movingVsrc_isLittleO_movingK.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_movingK_pos, eventually_three_le_movingVsrc] with
      x hbound hK hv
  rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
    Real.norm_of_nonneg hK.le] at hbound
  simpa using hbound

/-- The logarithmic part of (10.31).
@isnad1 id=eventual.0h0v.s5.fb70869fbf53 from=translated src=- shape=1e37f32d vocab=28c601f6
-/
theorem eventually_log_movingUtrPlus_le_half_K :
    ∀ᶠ x in atTop, Real.log (movingUtrPlus x) ≤ (1 / 2 : ℝ) * movingK x := by
  have hbound :=
    log_movingUtrPlus_isLittleO_movingK.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_movingK_pos, eventually_upper_transfer_ge_three] with
      x hbound hK hu
  rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
    Real.norm_of_nonneg hK.le] at hbound
  simpa using hbound

/-- The final inequality `u⁺_tr ≤ Z^(1/2)` in (10.31).
@isnad1 id=eventual.0h0v.s3.7d2795782eb7 from=translated src=- shape=68abfa87 vocab=20ca01c5
-/
theorem eventually_movingUtrPlus_le_sqrt_Z :
    ∀ᶠ x in atTop, movingUtrPlus x ≤ Real.sqrt (movingZ x) := by
  filter_upwards [eventually_log_movingUtrPlus_le_half_K,
      eventually_upper_transfer_ge_three] with x hlog hu
  calc
    movingUtrPlus x = Real.exp (Real.log (movingUtrPlus x)) :=
      (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (movingK x / 2) := by
      apply Real.exp_le_exp.mpr
      simpa [div_eq_mul_inv, mul_comm] using hlog
    _ = Real.sqrt (movingZ x) := by rw [movingZ, Real.exp_half]

/-! ### Unconditional decay of the named transfer error (10.33) -/

/--
@isnad1 id=isbigo.0h0v.s4.1c7e1edb5fc7 from=translated src=- shape=569d1b4b vocab=6c36174d
-/
theorem sqrt_scaleA_isBigO_scaleA_mul_sqrt :
    (fun x ↦ Real.sqrt (scaleA x)) =O[atTop]
      (fun x ↦ scaleA x * Real.sqrt (scaleA x)) := by
  apply IsBigO.of_bound 1
  filter_upwards [tendsto_scaleA_atTop.eventually_ge_atTop 1] with x hA
  have hsqrt0 : 0 ≤ Real.sqrt (scaleA x) := Real.sqrt_nonneg _
  have hprod0 : 0 ≤ scaleA x * Real.sqrt (scaleA x) := mul_nonneg (zero_le_one.trans hA) hsqrt0
  rw [Real.norm_of_nonneg hsqrt0, Real.norm_of_nonneg hprod0, one_mul]
  simpa using mul_le_mul_of_nonneg_right hA hsqrt0

/--
@isnad1 id=islittle.0h0v.s3.c281b81e7506 from=translated src=- shape=afbd0cda vocab=2e42ba8a
-/
theorem sqrt_scaleA_isLittleO_log2 :
    (fun x ↦ Real.sqrt (scaleA x)) =o[atTop] log2 :=
  sqrt_scaleA_isBigO_scaleA_mul_sqrt.trans_isLittleO scaleA_mul_sqrt_isLittleO_log2

/--
@isnad1 id=eq.3h1v.s6.cf6a0849a7d9 from=translated src=- shape=49f94744 vocab=e60c460f
-/
theorem sqrt_scaleL_div_log2_div_etaR_eq {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x) (hA : 0 < scaleA x) :
    Real.sqrt (scaleL x / log2 x) / movingEtaR x =
      Real.sqrt (scaleA x) / log2 x := by
  have hmain := movingTMain_div_etaR_eq hL hL2 hA
  unfold movingTMain at hmain
  calc
    Real.sqrt (scaleL x / log2 x) / movingEtaR x =
        (scaleA x * Real.sqrt (scaleL x / log2 x) / movingEtaR x) /
          scaleA x := by field_simp [hA.ne']
    _ = (scaleA x * Real.sqrt (scaleA x) / log2 x) / scaleA x := by rw [hmain]
    _ = Real.sqrt (scaleA x) / log2 x := by field_simp [hA.ne']

/--
@isnad1 id=islittle.0h0v.s4.e0fd4cd618b6 from=translated src=- shape=1c93d0b4 vocab=9651befe
-/
theorem sqrt_scaleL_div_log2_isLittleO_etaR :
    (fun x ↦ Real.sqrt (scaleL x / log2 x)) =o[atTop] movingEtaR := by
  have hzero : Tendsto (fun x ↦ Real.sqrt (scaleA x) / log2 x)
      atTop (nhds 0) := sqrt_scaleA_isLittleO_log2.tendsto_div_nhds_zero
  have hratio : Tendsto
      (fun x ↦ Real.sqrt (scaleL x / log2 x) / movingEtaR x)
      atTop (nhds 0) := by
    apply hzero.congr'
    filter_upwards [eventually_moving_core_positive] with x hcore
    exact (sqrt_scaleL_div_log2_div_etaR_eq hcore.1 hcore.2.1 hcore.2.2.1).symm
  refine isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_moving_core_positive] with x hcore
  have hetaR : 0 < movingEtaR x := mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1
  exact fun hzero ↦ (hetaR.ne' hzero).elim

/--
@isnad1 id=islittle.0h0v.s3.1a7ef5eb2e31 from=translated src=- shape=47806ae7 vocab=047b79f2
-/
theorem movingUtrPlus_isLittleO_etaR : movingUtrPlus =o[atTop] movingEtaR :=
  (movingUtrPlus_isBigO_scaleL_div_movingK.trans
      scaleL_div_movingK_isBigO_sqrt_ratio).trans_isLittleO
    sqrt_scaleL_div_log2_isLittleO_etaR

/--
@isnad1 id=eq.0h1v.s6.6f109855ddbb from=translated src=- shape=224c7deb vocab=584b5faa
-/
@[simp, nolint simpNF] theorem log_three_mul_movingZ_sq (x : ℝ) :
    Real.log (3 * movingZ x ^ 2) = Real.log 3 + 2 * movingK x := by
  have hZ : movingZ x ≠ 0 := (Real.exp_pos (movingK x)).ne'
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hZ), Real.log_pow, log_movingZ]
  norm_num

/--
@isnad1 id=tendsto.0h0v.s6.d44c800e7f59 from=translated src=- shape=59b88ee3 vocab=098110e6
-/
theorem log2_three_mul_movingZ_sq_div_etaR_tendsto_zero :
    Tendsto (fun x ↦ log2 (3 * movingZ x ^ 2) / movingEtaR x)
      atTop (nhds 0) := by
  have hKbound := movingK_isLittleO_scaleL.bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hhalfL : ∀ᶠ x in atTop, Real.log 3 ≤ (1 / 2 : ℝ) * scaleL x :=
    (tendsto_scaleL_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (Real.log 3)
  have hLlarge : ∀ᶠ x in atTop, 2 * Real.log 3 ≤ scaleL x := by
    filter_upwards [hhalfL] with x hx
    linarith
  apply squeeze_zero'
  · filter_upwards [eventually_moving_core_positive, eventually_movingK_pos,
        tendsto_movingK_atTop.eventually_ge_atTop 1] with x hcore hK hKone
    have hinner : 1 ≤ Real.log 3 + 2 * movingK x := by
      have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      linarith
    have hnum : 0 ≤ log2 (3 * movingZ x ^ 2) := by
      rw [log2_eq, log_three_mul_movingZ_sq]
      exact Real.log_nonneg hinner
    exact div_nonneg hnum (mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1).le
  · filter_upwards [eventually_moving_core_positive, eventually_movingK_pos,
        hKbound, hLlarge] with x hcore hK hKbound hLlarge
    have hKle : movingK x ≤ (1 / 4 : ℝ) * scaleL x := by
      rw [Real.norm_of_nonneg hK.le, Real.norm_of_nonneg hcore.1.le] at hKbound
      exact hKbound
    have hinnerPos : 0 < Real.log 3 + 2 * movingK x := by
      have : 0 < Real.log 3 := Real.log_pos (by norm_num)
      positivity
    have hinnerLe : Real.log 3 + 2 * movingK x ≤ scaleL x := by linarith
    have hnumLe : log2 (3 * movingZ x ^ 2) ≤ log2 x := by
      rw [log2_eq, log_three_mul_movingZ_sq, log2_eq, scaleL] at *
      exact Real.log_le_log hinnerPos hinnerLe
    exact div_le_div_of_nonneg_right hnumLe
      (mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1).le
  · exact log2_isLittleO_etaR.tendsto_div_nhds_zero

/--
@isnad1 id=tendsto.0h0v.s5.32b01aa4e9d1 from=translated src=- shape=b1eb4ff5 vocab=46e84ab4
-/
theorem movingUtrPlus_log_div_etaR_tendsto_zero :
    Tendsto (fun x ↦
      (movingUtrPlus x / Real.log (movingUtrPlus x)) / movingEtaR x)
      atTop (nhds 0) := by
  have hu : Tendsto (fun x ↦ movingUtrPlus x / movingEtaR x)
      atTop (nhds 0) := movingUtrPlus_isLittleO_etaR.tendsto_div_nhds_zero
  have hloginv : Tendsto (fun x ↦ (Real.log (movingUtrPlus x))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_movingUtrPlus_atTop)
  have hprod := hu.mul hloginv
  have ht : Tendsto (fun x ↦
      (movingUtrPlus x / Real.log (movingUtrPlus x)) / movingEtaR x)
      atTop (nhds (0 * 0)) := by
    apply hprod.congr'
    filter_upwards [eventually_moving_core_positive, eventually_upper_transfer_ge_three] with
        x hcore hut
    have hetaR : movingEtaR x ≠ 0 :=
      (mul_pos hcore.2.2.2.2.1 hcore.2.2.2.1).ne'
    have hlog : Real.log (movingUtrPlus x) ≠ 0 :=
      (Real.log_pos (by linarith)).ne'
    field_simp [hetaR, hlog]
  simpa using ht

/-- Lemma 10.18's error limit, with every term of (10.33) discharged.
@isnad1 id=tendsto.0h1v.s4.00c3bc4e4465 from=translated src=- shape=584f33b3 vocab=17d8b2f6
-/
theorem movingTransferError_tendsto_zero_unconditional (C : ℝ) :
    Tendsto (movingTransferError C) atTop (nhds 0) :=
  movingTransferError_tendsto_zero
    log2_three_mul_movingZ_sq_div_etaR_tendsto_zero
    movingUtrPlus_log_div_etaR_tendsto_zero

end

end RankAmplification
