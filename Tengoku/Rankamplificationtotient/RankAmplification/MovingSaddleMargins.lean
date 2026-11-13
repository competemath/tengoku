import Tengoku.Rankamplificationtotient.RankAmplification.MovingScales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Second-order moving saddle margins This file supplies the second-order inequalities isolated as `HasMovingSaddleMargins` in the moving-scale bookkeeping. -/

namespace RankAmplification

open Filter
open Asymptotics
open scoped Asymptotics Topology

noncomputable section

/-- The error removed from `L/2` in the source threshold.-/
def movingSourceLoss (x : ℝ) : ℝ :=
  2 * (movingJ x : ℝ) * movingK x + (movingJ x : ℝ) * Real.log 2

/--
@isnad1 id=eq.0h1v.s5.f3df306fa51e from=translated src=- shape=9c9f1d81 vocab=4921a8ed
-/
theorem movingSourceLogThreshold_eq (x : ℝ) :
    movingSourceLogThreshold x = (1 / 2 : ℝ) * scaleL x - movingSourceLoss x := by
  simp [movingSourceLogThreshold, movingSourceLoss]
  ring

/--
@isnad1 id=islittle.0h0v.s3.24cdc991ae69 from=translated src=- shape=47806ae7 vocab=617761f6
-/
theorem movingEtaR_isLittleO_etaL : movingEtaR =o[atTop] movingEtaL := by
  have h := movingR_isLittleO_scaleL.mul_isBigO (isBigO_refl movingEta atTop)
  apply h.congr'
  · filter_upwards [] with x
    simp [movingEtaR, mul_comm]
  · filter_upwards [] with x
    simp [movingEtaL, mul_comm]

/--
@isnad1 id=islittle.0h0v.s5.50dda52118a0 from=translated src=- shape=080c0d74 vocab=aeca5692
-/
theorem movingJ_mul_log_two_isLittleO_etaR :
    (fun x ↦ (movingJ x : ℝ) * Real.log 2) =o[atTop] movingEtaR := by
  have hsmall :
      (fun x ↦ (movingJ x : ℝ) * Real.log 2) =O[atTop]
        (fun x ↦ (movingJ x : ℝ) ^ 2 * log2 x) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_two_le_movingJ, eventually_log2_pos,
        tendsto_log2_atTop.eventually_ge_atTop (Real.log 2)] with x hJ hL2 hlog2
    have hJ0 : 0 ≤ (movingJ x : ℝ) := by positivity
    have hleft : 0 ≤ (movingJ x : ℝ) * Real.log 2 :=
      mul_nonneg hJ0 (Real.log_nonneg (by norm_num))
    have hright : 0 ≤ (movingJ x : ℝ) ^ 2 * log2 x :=
      mul_nonneg (sq_nonneg _) hL2.le
    rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright, one_mul]
    calc
      (movingJ x : ℝ) * Real.log 2 ≤ (movingJ x : ℝ) * log2 x :=
        mul_le_mul_of_nonneg_left hlog2 hJ0
      _ ≤ (movingJ x : ℝ) ^ 2 * log2 x := by
        have hJone : (1 : ℝ) ≤ movingJ x := by exact_mod_cast (show 1 ≤ movingJ x by omega)
        nlinarith
  exact hsmall.trans_isLittleO movingJ_sq_mul_log2_isLittleO_etaR

/--
@isnad1 id=islittle.0h0v.s5.395fc2995e63 from=translated src=- shape=080c0d74 vocab=c0b4487d
-/
theorem movingJ_mul_log_two_isLittleO_etaL :
    (fun x ↦ (movingJ x : ℝ) * Real.log 2) =o[atTop] movingEtaL :=
  movingJ_mul_log_two_isLittleO_etaR.trans movingEtaR_isLittleO_etaL

/--
@isnad1 id=islittle.0h0v.s3.1be8ba03e786 from=translated src=- shape=47806ae7 vocab=7d4e20f2
-/
theorem movingSourceLoss_isLittleO_etaL : movingSourceLoss =o[atTop] movingEtaL := by
  have hJK := movingJ_mul_K_isLittleO_etaL.const_mul_left 2
  have hsum := hJK.add movingJ_mul_log_two_isLittleO_etaL
  apply hsum.congr_left
  intro x
  simp [movingSourceLoss]
  ring

/--
@isnad1 id=islittle.0h0v.s4.bc91400cb977 from=translated src=- shape=3116060c vocab=7659ca09
-/
theorem log3_mul_sqrt_scaleA_isLittleO_log2 :
    (fun x ↦ log3 x * Real.sqrt (scaleA x)) =o[atTop] log2 := by
  have hbig := scaleA_isEquivalent_log3.symm.isBigO.mul
    (isBigO_refl (fun x ↦ Real.sqrt (scaleA x)) atTop)
  have hlittle := hbig.trans_isLittleO scaleA_mul_sqrt_isLittleO_log2
  apply hlittle.congr'
  · exact EventuallyEq.rfl
  · filter_upwards [] with x
    rfl

/--
@isnad1 id=eventual.0h0v.s5.260088a5df45 from=translated src=- shape=8e106e86 vocab=470d521a
-/
theorem eventually_log3_le_eta_mul_log2_div_two :
    ∀ᶠ x in atTop, log3 x ≤ movingEta x * log2 x / 2 := by
  have hbound :=
    log3_mul_sqrt_scaleA_isLittleO_log2.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_log3_pos, eventually_log2_pos,
      eventually_scaleA_pos] with x hbound hL3 hL2 hA
  rw [Real.norm_of_nonneg (mul_nonneg hL3.le (Real.sqrt_nonneg _)),
    Real.norm_of_nonneg hL2.le] at hbound
  have hsqrt : 0 < Real.sqrt (scaleA x) := Real.sqrt_pos.2 hA
  unfold movingEta
  have hdiv : log3 x ≤ (log2 x / 2) / Real.sqrt (scaleA x) :=
    (le_div_iff₀ hsqrt).2 (by nlinarith)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/--
@isnad1 id=islittle.0h0v.s4.9e16d124ea4a from=translated src=- shape=ed61af91 vocab=a6bd2e7f
-/
theorem scaleA_mul_log2_isLittleO_scaleL :
    (fun x ↦ scaleA x * log2 x) =o[atTop] scaleL := by
  have h := scaleA_isLittleO_log2.mul_isBigO (isBigO_refl log2 atTop)
  have hsq : (fun x ↦ scaleA x * log2 x) =o[atTop]
      (fun x ↦ log2 x ^ 2) := by
    apply h.congr_right
    intro x
    rw [pow_two]
  exact hsq.trans
    (log2_sq_isLittleO_sqrt_scaleL.trans_isBigO sqrt_scaleL_isBigO_scaleL)

/--
@isnad1 id=eq.3h1v.s6.6cbf5ee6ac00 from=translated src=- shape=fd770bfa vocab=fc398411
-/
theorem eta_mul_sqrt_ratio_sq {x : ℝ}
    (hL : 0 ≤ scaleL x) (hL2 : 0 < log2 x) (hA : 0 < scaleA x) :
    (movingEta x * Real.sqrt (scaleL x / log2 x)) ^ 2 =
      scaleL x / (scaleA x * log2 x) := by
  have hAsq : Real.sqrt (scaleA x) ^ 2 = scaleA x := Real.sq_sqrt hA.le
  have hRsq : Real.sqrt (scaleL x / log2 x) ^ 2 = scaleL x / log2 x :=
    Real.sq_sqrt (div_nonneg hL hL2.le)
  unfold movingEta
  rw [mul_pow, inv_pow, hAsq, hRsq]
  field_simp [hA.ne', hL2.ne']

/--
@isnad1 id=eventual.0h0v.s5.38d7c6d0686b from=translated src=- shape=c39e19af vocab=b0569d43
-/
theorem eventually_three_le_eta_mul_sqrt_ratio :
    ∀ᶠ x in atTop,
      3 ≤ movingEta x * Real.sqrt (scaleL x / log2 x) := by
  have hbound := scaleA_mul_log2_isLittleO_scaleL.bound
    (by norm_num : (0 : ℝ) < 1 / 9)
  filter_upwards [hbound, eventually_moving_core_positive] with x hbound hcore
  rw [Real.norm_of_nonneg (mul_nonneg hcore.2.2.1.le hcore.2.1.le),
    Real.norm_of_nonneg hcore.1.le] at hbound
  have hprod : 9 * (scaleA x * log2 x) ≤ scaleL x := by linarith
  have hsqrtNonneg :
      0 ≤ movingEta x * Real.sqrt (scaleL x / log2 x) :=
    mul_nonneg hcore.2.2.2.2.1.le (Real.sqrt_nonneg _)
  have hsq := eta_mul_sqrt_ratio_sq hcore.1.le hcore.2.1 hcore.2.2.1
  have hden : 0 < scaleA x * log2 x := mul_pos hcore.2.2.1 hcore.2.1
  have hsqNine : 9 ≤
      (movingEta x * Real.sqrt (scaleL x / log2 x)) ^ 2 := by
    rw [hsq]
    exact (le_div_iff₀ hden).2 hprod
  nlinarith

/--
@isnad1 id=le.3h1v.s6.59f2f74bf1af from=translated src=- shape=99c53a99 vocab=bbc1406d
-/
theorem movingSqrtRatio_mul_K_ge_quarter_L {x : ℝ}
    (hL : 0 < scaleL x) (hL2 : 0 < log2 x)
    (hRatio : (1 / 3 : ℝ) ≤ movingK x / movingR x) :
    (1 / 4 : ℝ) * scaleL x ≤
      Real.sqrt (scaleL x / log2 x) * movingK x := by
  have hR := movingR_pos hL hL2
  have hid := scaleL_div_movingR_eq_sqrt_div hL hL2
  have hKR : (1 / 3 : ℝ) * movingR x ≤ movingK x := by
    apply (le_div_iff₀ hR).mp
    simpa [mul_comm] using hRatio
  rw [← hid]
  have hL0 := hL.le
  calc
    (1 / 4 : ℝ) * scaleL x ≤ (1 / 3 : ℝ) * scaleL x := by nlinarith
    _ = (scaleL x / movingR x) * ((1 / 3 : ℝ) * movingR x) := by
      field_simp [hR.ne']
    _ ≤ (scaleL x / movingR x) * movingK x :=
      mul_le_mul_of_nonneg_left hKR (div_nonneg hL0 hR.le)

/-- The source and transfer margins (10.34) hold for all sufficiently large arguments.
@isnad1 id=eventual.0h0v.s3.8087dd0ad1ef from=translated src=- shape=07c3c963 vocab=afa25697
-/
theorem eventually_hasMovingSaddleMargins :
    ∀ᶠ x in atTop, HasMovingSaddleMargins x := by
  have hloss := movingSourceLoss_isLittleO_etaL.bound (by norm_num : (0 : ℝ) < 1 / 8)
  have hKratio := tendsto_movingK_div_R_half.eventually
    (Ici_mem_nhds (show (1 / 3 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [eventually_moving_core_positive, eventually_movingK_pos,
      eventually_movingEta_lt (1 / 8) (by norm_num), eventually_two_le_movingJ,
      eventually_log3_le_eta_mul_log2_div_two,
      eventually_three_le_eta_mul_sqrt_ratio, hloss, hKratio] with
      x hcore hK heta hJ hlog hetaRoot hloss hKratio
  have hR := hcore.2.2.2.1
  have hetaPos := hcore.2.2.2.2.1
  have hetaLPos : 0 < movingEtaL x := mul_pos hetaPos hcore.1
  have hsourceLossNonneg : 0 ≤ movingSourceLoss x := by
    unfold movingSourceLoss
    positivity
  rw [Real.norm_of_nonneg hsourceLossNonneg,
    Real.norm_of_nonneg hetaLPos.le] at hloss
  have hKle : movingK x ≤ movingK0 x :=
    movingK_le_K0 hcore.2.2.2.2.2.2.2 hcore.2.2.2.2.2.2.1.le
  let r : ℝ := Real.sqrt (scaleL x / log2 x)
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos hcore.1 hcore.2.1)
  have hrK : (1 / 4 : ℝ) * scaleL x ≤ r * movingK x :=
    movingSqrtRatio_mul_K_ge_quarter_L hcore.1 hcore.2.1 hKratio
  have hlossDiv : movingSourceLoss x / movingK x ≤ (1 / 2 : ℝ) * movingEta x * r := by
    apply (div_le_iff₀ hK).2
    have hsmall : movingSourceLoss x ≤ (1 / 8 : ℝ) * movingEta x * scaleL x := by
      simpa [movingEtaL, mul_assoc] using hloss
    calc
      movingSourceLoss x ≤ (1 / 8 : ℝ) * movingEta x * scaleL x := hsmall
      _ ≤ ((1 / 2 : ℝ) * movingEta x * r) * movingK x := by
        have hrK0 : 0 ≤ r * movingK x := (mul_pos hr hK).le
        nlinarith [mul_nonneg hetaPos.le hrK0]
  have hbase : scaleL x / (2 * movingK x) ≥
      (1 + (7 / 2 : ℝ) * movingEta x) * r := by
    have hcoef : 0 < 1 - 4 * movingEta x := by linarith
    have h2K : 2 * movingK x ≤ (1 - 4 * movingEta x) * movingR x := by
      unfold movingK0 at hKle
      nlinarith
    have hden : 0 < 2 * movingK x := by positivity
    have hq : scaleL x / ((1 - 4 * movingEta x) * movingR x) ≤
        scaleL x / (2 * movingK x) := by
      exact div_le_div_of_nonneg_left hcore.1.le hden h2K
    have heq : scaleL x / ((1 - 4 * movingEta x) * movingR x) =
        r / (1 - 4 * movingEta x) := by
      change scaleL x / ((1 - 4 * movingEta x) * movingR x) =
        Real.sqrt (scaleL x / log2 x) / (1 - 4 * movingEta x)
      rw [← scaleL_div_movingR_eq_sqrt_div hcore.1 hcore.2.1]
      field_simp [hR.ne', hcoef.ne']
    rw [heq] at hq
    have haux : (1 + (7 / 2 : ℝ) * movingEta x) * r ≤
        r / (1 - 4 * movingEta x) := by
      apply (le_div_iff₀ hcoef).2
      nlinarith [mul_pos hetaPos hr]
    exact haux.trans hq
  have hvLower : (1 + 3 * movingEta x) * r ≤ movingVsrc x := by
    rw [movingVsrc_eq_sourceLog_div, movingSourceLogThreshold_eq]
    have heq : ((1 / 2 : ℝ) * scaleL x - movingSourceLoss x) / movingK x =
        scaleL x / (2 * movingK x) - movingSourceLoss x / movingK x := by ring
    rw [heq]
    linarith
  have hlogr : Real.log r = (log2 x - log3 x) / 2 := by
    change Real.log (Real.sqrt (scaleL x / log2 x)) = (log2 x - log3 x) / 2
    rw [Real.log_sqrt (div_nonneg hcore.1.le hcore.2.1.le),
      Real.log_div hcore.1.ne' hcore.2.1.ne']
    change (log2 x - log3 x) / 2 = (log2 x - log3 x) / 2
    rfl
  have hlogLower : (1 / 2 - movingEta x / 4) * log2 x ≤ Real.log r := by
    rw [hlogr]
    nlinarith
  have hrOne : 1 < r := by
    have hlog2pos : 0 < Real.log r := by
      have hcoefPos : 0 < (1 / 2 - movingEta x / 4) := by linarith
      have : 0 < (1 / 2 - movingEta x / 4) * log2 x :=
        mul_pos hcoefPos hcore.2.1
      linarith
    exact (Real.log_pos_iff hr.le).mp hlog2pos
  have hfactorOne : 1 ≤ 1 + 3 * movingEta x := by linarith
  have hrV : r ≤ movingVsrc x :=
    (le_mul_of_one_le_left hr.le hfactorOne).trans hvLower
  have hvPos : 0 < movingVsrc x := hr.trans_le hrV
  have hlogV : Real.log r ≤ Real.log (movingVsrc x) :=
    Real.log_le_log hr hrV
  have hrL2 : r * log2 x = movingR x := by
    have h := ((div_eq_iff hr.ne').mp
      (movingR_div_sqrt_div_eq_log2 hcore.1 hcore.2.1)).symm
    simpa [mul_comm] using h
  have hsaddleCoef : (1 / 2 + movingEta x) * movingR x ≤
      ((1 + 3 * movingEta x) * r) *
        ((1 / 2 - movingEta x / 4) * log2 x) := by
    have hcoeff : (1 / 2 + movingEta x) ≤
        (1 + 3 * movingEta x) * (1 / 2 - movingEta x / 4) := by
      nlinarith [mul_pos hetaPos (show 0 < 1 - 3 * movingEta x by linarith)]
    calc
      (1 / 2 + movingEta x) * movingR x =
          (1 / 2 + movingEta x) * (r * log2 x) := by rw [hrL2]
      _ ≤ ((1 + 3 * movingEta x) * (1 / 2 - movingEta x / 4)) *
          (r * log2 x) :=
        mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hr.le hcore.2.1.le)
      _ = ((1 + 3 * movingEta x) * r) *
          ((1 / 2 - movingEta x / 4) * log2 x) := by ring
  have htargetCommon : movingK x + 3 * movingEtaR x ≤
      (1 / 2 + movingEta x) * movingR x := by
    calc
      movingK x + 3 * movingEtaR x ≤ movingK0 x + 3 * movingEtaR x :=
        add_le_add hKle le_rfl
      _ = (1 / 2 + movingEta x) * movingR x := by
        simp only [movingK0, movingEtaR]
        ring
  have hsourceMargin :
      movingK x + 3 * movingEtaR x ≤
        movingVsrc x * Real.log (movingVsrc x) := by
    have hprodLower :
        ((1 + 3 * movingEta x) * r) *
            ((1 / 2 - movingEta x / 4) * log2 x) ≤
          movingVsrc x * Real.log (movingVsrc x) := by
      have hlogLower0 : 0 ≤ (1 / 2 - movingEta x / 4) * log2 x := by
        exact (mul_pos (by linarith) hcore.2.1).le
      exact mul_le_mul hvLower (hlogLower.trans hlogV) hlogLower0 hvPos.le
    exact htargetCommon.trans (hsaddleCoef.trans hprodLower)
  have huLower : (1 + 3 * movingEta x) * r ≤ movingUtrMinus x := by
    unfold movingUtrMinus
    have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hform : (scaleL x - 3 * movingK x + Real.log 2) / (2 * movingK x) ≥
        scaleL x / (2 * movingK x) - 3 / 2 := by
      field_simp [hK.ne']
      nlinarith
    have hsubtract : (3 / 2 : ℝ) ≤ (1 / 2 : ℝ) * movingEta x * r := by
      nlinarith
    linarith
  have hrU : r ≤ movingUtrMinus x :=
    (le_mul_of_one_le_left hr.le hfactorOne).trans huLower
  have huPos : 0 < movingUtrMinus x := hr.trans_le hrU
  have hlogU : Real.log r ≤ Real.log (movingUtrMinus x) :=
    Real.log_le_log hr hrU
  have htransferMargin :
      movingK x + 3 * movingEtaR x ≤
        movingUtrMinus x * Real.log (movingUtrMinus x) := by
    have hprodLower :
        ((1 + 3 * movingEta x) * r) *
            ((1 / 2 - movingEta x / 4) * log2 x) ≤
          movingUtrMinus x * Real.log (movingUtrMinus x) := by
      have hlogLower0 : 0 ≤ (1 / 2 - movingEta x / 4) * log2 x := by
        have hc : 0 ≤ 1 / 2 - movingEta x / 4 := by linarith
        exact mul_nonneg hc hcore.2.1.le
      exact mul_le_mul huLower (hlogLower.trans hlogU) hlogLower0 huPos.le
    exact htargetCommon.trans (hsaddleCoef.trans hprodLower)
  exact ⟨hsourceMargin, htransferMargin⟩

end

end RankAmplification
