import Tengoku.Rankamplificationtotient.RankAmplification.Saddle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed-rank cutoffs This module records the exact cutoff identities used in Theorems 1.1 and 10.14. -/

namespace RankAmplification

open Filter
open scoped Topology

noncomputable section

/-! ## Exact real cutoffs -/

/-- The lower fixed-rank cutoff `y_J = exp(T_J)`.-/
def fixedRankY (J : ℕ) (x : ℝ) : ℝ :=
  Real.exp (fixedRankT J x)

/-- The upper fixed-rank cutoff, written in the form `exp(J T_J)`.-/
def fixedRankUpperY (J : ℕ) (x : ℝ) : ℝ :=
  Real.exp (J * fixedRankT J x)

@[simp] theorem fixedRankY_pos (J : ℕ) (x : ℝ) :
    0 < fixedRankY J x := by
  unfold fixedRankY
  positivity

@[simp] theorem fixedRankUpperY_pos (J : ℕ) (x : ℝ) :
    0 < fixedRankUpperY J x := by
  unfold fixedRankUpperY
  positivity

/-- The paper's exact identity `Y_J = y_J^J`.-/
theorem fixedRankUpperY_eq_pow (J : ℕ) (x : ℝ) :
    fixedRankUpperY J x = fixedRankY J x ^ J := by
  unfold fixedRankUpperY fixedRankY
  exact Real.exp_nat_mul (fixedRankT J x) J

/-- The exponent of `Y_J` is exactly `√J G`.-/
theorem fixedRankUpperY_eq_exp_sqrt_mul_scaleG {J : ℕ} (x : ℝ)
    (hJ : 0 < J) :
    fixedRankUpperY J x = Real.exp (Real.sqrt J * scaleG x) := by
  unfold fixedRankUpperY
  rw [nat_mul_fixedRankT hJ]

/-- The lower exponent multiplied by `√J` recovers `G`.-/
theorem fixedRankY_sqrt_exponent {J : ℕ} (x : ℝ) (hJ : 0 < J) :
    Real.sqrt J * Real.log (fixedRankY J x) = scaleG x := by
  rw [fixedRankY, Real.log_exp, sqrt_mul_fixedRankT hJ]

/-- The upper cutoff has logarithm `√J G`.-/
theorem log_fixedRankUpperY {J : ℕ} (x : ℝ) (hJ : 0 < J) :
    Real.log (fixedRankUpperY J x) = Real.sqrt J * scaleG x := by
  rw [fixedRankUpperY_eq_exp_sqrt_mul_scaleG x hJ, Real.log_exp]

/-- For positive `T_J` and positive rank, the lower cutoff does not exceed the upper cutoff.-/
theorem fixedRankY_le_upperY {J : ℕ} {x : ℝ}
    (hJ : 0 < J) (hT : 0 ≤ fixedRankT J x) :
    fixedRankY J x ≤ fixedRankUpperY J x := by
  unfold fixedRankY fixedRankUpperY
  apply Real.exp_le_exp.mpr
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  nlinarith

/-! ## Natural cutoffs -/

/-- Natural lower cutoff obtained by flooring `y_J`.-/
def fixedRankNatY (J x : ℕ) : ℕ :=
  ⌊fixedRankY J (x : ℝ)⌋₊

/-- Natural upper cutoff obtained by flooring `Y_J`.-/
def fixedRankNatUpperY (J x : ℕ) : ℕ :=
  ⌊fixedRankUpperY J (x : ℝ)⌋₊

@[simp] theorem fixedRankNatY_eq_floor (J x : ℕ) :
    fixedRankNatY J x = ⌊fixedRankY J (x : ℝ)⌋₊ := rfl

@[simp] theorem fixedRankNatUpperY_eq_floor (J x : ℕ) :
    fixedRankNatUpperY J x = ⌊fixedRankUpperY J (x : ℝ)⌋₊ := rfl

theorem fixedRankNatY_le_upperY {J x : ℕ} (hJ : 0 < J)
    (hT : 0 ≤ fixedRankT J (x : ℝ)) :
    fixedRankNatY J x ≤ fixedRankNatUpperY J x := by
  exact Nat.floor_mono (fixedRankY_le_upperY hJ hT)

/-- `T_J` tends to infinity for every fixed positive rank.-/
theorem tendsto_fixedRankT_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankT J) atTop atTop := by
  unfold fixedRankT
  exact tendsto_scaleG_atTop.atTop_div_const
    (Real.sqrt_pos.2 (by exact_mod_cast hJ))

/-- The real lower cutoff tends to infinity.-/
theorem tendsto_fixedRankY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankY J) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp (tendsto_fixedRankT_atTop J hJ)

/-- The real upper cutoff tends to infinity.-/
theorem tendsto_fixedRankUpperY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankUpperY J) atTop atTop := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold fixedRankUpperY
  exact Real.tendsto_exp_atTop.comp
    ((tendsto_fixedRankT_atTop J hJ).const_mul_atTop hJreal)

/-- Natural lower cutoffs tend to infinity along natural size parameters.-/
theorem tendsto_fixedRankNatY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankNatY J) atTop atTop := by
  have hreal : Tendsto (fun x : ℕ ↦ fixedRankY J (x : ℝ)) atTop atTop :=
    (tendsto_fixedRankY_atTop J hJ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_nat_floor_atTop.comp hreal

/-- Natural upper cutoffs tend to infinity along natural size parameters.-/
theorem tendsto_fixedRankNatUpperY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankNatUpperY J) atTop atTop := by
  have hreal : Tendsto (fun x : ℕ ↦ fixedRankUpperY J (x : ℝ)) atTop atTop :=
    (tendsto_fixedRankUpperY_atTop J hJ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_nat_floor_atTop.comp hreal

theorem eventually_three_le_fixedRankNatY (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, 3 ≤ fixedRankNatY J x :=
  (tendsto_fixedRankNatY_atTop J hJ).eventually_ge_atTop 3

theorem eventually_three_le_fixedRankNatUpperY (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, 3 ≤ fixedRankNatUpperY J x :=
  (tendsto_fixedRankNatUpperY_atTop J hJ).eventually_ge_atTop 3

theorem eventually_fixedRankNatY_le_upperY (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatY J x ≤ fixedRankNatUpperY J x := by
  have hT : ∀ᶠ x : ℕ in atTop, 0 ≤ fixedRankT J (x : ℝ) :=
    ((tendsto_fixedRankT_atTop J hJ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 0
  filter_upwards [hT] with x hx
  exact fixedRankNatY_le_upperY hJ hx

/-! ## The fixed-rank error scale -/

/-- In the positive range, `V/G = 1/A`.-/
theorem scaleV_div_scaleG_eq_inv_scaleA {x : ℝ}
    (hL : 0 < scaleL x) (hA : 0 < scaleA x) :
    scaleV x / scaleG x = (scaleA x)⁻¹ := by
  have hG : 0 < scaleG x := scaleG_pos hL hA
  have hsq : scaleG x ^ 2 = scaleL x * scaleA x :=
    scaleG_sq hL.le hA.le
  rw [scaleV_eq]
  field_simp [hG.ne', hA.ne']
  nlinarith

/-- The ratio `V/G` tends to zero.-/
theorem tendsto_scaleV_div_scaleG_zero :
    Tendsto (fun x ↦ scaleV x / scaleG x) atTop (nhds 0) := by
  have hinv : Tendsto (fun x ↦ (scaleA x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_scaleA_atTop
  apply hinv.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  exact (scaleV_div_scaleG_eq_inv_scaleA hL hA).symm

/-- The fixed-rank secondary scale satisfies the paper's `V=o(G)`.-/
theorem scaleV_isLittleO_scaleG : scaleV =o[atTop] scaleG := by
  refine Asymptotics.isLittleO_of_tendsto' ?_ tendsto_scaleV_div_scaleG_zero
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  intro hzero
  exact ((scaleG_pos hL hA).ne' hzero).elim

/-- Any fixed multiple of `V` is still negligible compared with `G`.-/
theorem const_mul_scaleV_isLittleO_scaleG (c : ℝ) :
    (fun x ↦ c * scaleV x) =o[atTop] scaleG :=
  scaleV_isLittleO_scaleG.const_mul_left c

/-- A positive fixed margin in the main exponent eventually absorbs any fixed multiple of `V`.-/
theorem eventually_const_mul_scaleV_le_margin_scaleG
    {c margin : ℝ} (hmargin : 0 < margin) :
    ∀ᶠ x : ℝ in atTop, c * scaleV x ≤ margin * scaleG x := by
  have hbound := (const_mul_scaleV_isLittleO_scaleG c).bound hmargin
  filter_upwards [hbound, eventually_scaleL_pos, eventually_scaleA_pos] with x hx hL hA
  have hG : 0 ≤ scaleG x := (scaleG_pos hL hA).le
  have habs : c * scaleV x ≤ ‖c * scaleV x‖ := Real.le_norm_self _
  exact habs.trans (hx.trans_eq (by rw [Real.norm_of_nonneg hG]))

end

end RankAmplification
