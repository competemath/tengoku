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

/--
@isnad1 id=lt.0h2v.s4.1b8ee3b589e1 from=translated src=- shape=787c1379 vocab=c6d01bb9
-/
@[simp] theorem fixedRankY_pos (J : ℕ) (x : ℝ) :
    0 < fixedRankY J x := by
  unfold fixedRankY
  positivity

/--
@isnad1 id=lt.0h2v.s4.76f0fa7e86cd from=translated src=- shape=787c1379 vocab=0658c632
-/
@[simp] theorem fixedRankUpperY_pos (J : ℕ) (x : ℝ) :
    0 < fixedRankUpperY J x := by
  unfold fixedRankUpperY
  positivity

/-- The paper's exact identity `Y_J = y_J^J`.
@isnad1 id=eq.0h2v.s4.35ec9aa54e8a from=translated src=- shape=6bda3f1c vocab=a0690978
-/
theorem fixedRankUpperY_eq_pow (J : ℕ) (x : ℝ) :
    fixedRankUpperY J x = fixedRankY J x ^ J := by
  unfold fixedRankUpperY fixedRankY
  exact Real.exp_nat_mul (fixedRankT J x) J

/-- The exponent of `Y_J` is exactly `√J G`.
@isnad1 id=eq.1h2v.s5.63579afd9857 from=translated src=- shape=1d19f84d vocab=66982cdd
-/
theorem fixedRankUpperY_eq_exp_sqrt_mul_scaleG {J : ℕ} (x : ℝ)
    (hJ : 0 < J) :
    fixedRankUpperY J x = Real.exp (Real.sqrt J * scaleG x) := by
  unfold fixedRankUpperY
  rw [nat_mul_fixedRankT hJ]

/-- The lower exponent multiplied by `√J` recovers `G`.
@isnad1 id=eq.1h2v.s5.bb91d06498f7 from=translated src=- shape=69d1a3ad vocab=6bfa4963
-/
theorem fixedRankY_sqrt_exponent {J : ℕ} (x : ℝ) (hJ : 0 < J) :
    Real.sqrt J * Real.log (fixedRankY J x) = scaleG x := by
  rw [fixedRankY, Real.log_exp, sqrt_mul_fixedRankT hJ]

/-- The upper cutoff has logarithm `√J G`.
@isnad1 id=eq.1h2v.s5.e3438b55a450 from=translated src=- shape=7487648f vocab=5b1cd83c
-/
theorem log_fixedRankUpperY {J : ℕ} (x : ℝ) (hJ : 0 < J) :
    Real.log (fixedRankUpperY J x) = Real.sqrt J * scaleG x := by
  rw [fixedRankUpperY_eq_exp_sqrt_mul_scaleG x hJ, Real.log_exp]

/-- For positive `T_J` and positive rank, the lower cutoff does not exceed the upper cutoff.
@isnad1 id=le.2h2v.s5.45d987032abe from=translated src=- shape=963d054c vocab=fa26137c
-/
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

/--
@isnad1 id=eq.0h2v.s4.a20192d40020 from=translated src=- shape=dd00509d vocab=4b117e6d
-/
@[simp] theorem fixedRankNatY_eq_floor (J x : ℕ) :
    fixedRankNatY J x = ⌊fixedRankY J (x : ℝ)⌋₊ := rfl

/--
@isnad1 id=eq.0h2v.s4.a11e14f540c5 from=translated src=- shape=dd00509d vocab=e96686c0
-/
@[simp] theorem fixedRankNatUpperY_eq_floor (J x : ℕ) :
    fixedRankNatUpperY J x = ⌊fixedRankUpperY J (x : ℝ)⌋₊ := rfl

/--
@isnad1 id=le.2h2v.s5.0a8f843e8da9 from=translated src=- shape=8aec7b74 vocab=257a9742
-/
theorem fixedRankNatY_le_upperY {J x : ℕ} (hJ : 0 < J)
    (hT : 0 ≤ fixedRankT J (x : ℝ)) :
    fixedRankNatY J x ≤ fixedRankNatUpperY J x := by
  exact Nat.floor_mono (fixedRankY_le_upperY hJ hT)

/-- `T_J` tends to infinity for every fixed positive rank.
@isnad1 id=tendsto.1h1v.s4.97cc250a8b1a from=translated src=- shape=4e3c1c3f vocab=450f3b24
-/
theorem tendsto_fixedRankT_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankT J) atTop atTop := by
  unfold fixedRankT
  exact tendsto_scaleG_atTop.atTop_div_const
    (Real.sqrt_pos.2 (by exact_mod_cast hJ))

/-- The real lower cutoff tends to infinity.
@isnad1 id=tendsto.1h1v.s4.87d9b1a3aa6c from=translated src=- shape=4e3c1c3f vocab=22f3da44
-/
theorem tendsto_fixedRankY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankY J) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp (tendsto_fixedRankT_atTop J hJ)

/-- The real upper cutoff tends to infinity.
@isnad1 id=tendsto.1h1v.s4.469a1aab5b0c from=translated src=- shape=4e3c1c3f vocab=b1a70b6e
-/
theorem tendsto_fixedRankUpperY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankUpperY J) atTop atTop := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold fixedRankUpperY
  exact Real.tendsto_exp_atTop.comp
    ((tendsto_fixedRankT_atTop J hJ).const_mul_atTop hJreal)

/-- Natural lower cutoffs tend to infinity along natural size parameters.
@isnad1 id=tendsto.1h1v.s4.ed0bf9528a1f from=translated src=- shape=52e44ca1 vocab=63397b5e
-/
theorem tendsto_fixedRankNatY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankNatY J) atTop atTop := by
  have hreal : Tendsto (fun x : ℕ ↦ fixedRankY J (x : ℝ)) atTop atTop :=
    (tendsto_fixedRankY_atTop J hJ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_nat_floor_atTop.comp hreal

/-- Natural upper cutoffs tend to infinity along natural size parameters.
@isnad1 id=tendsto.1h1v.s4.9a867d15fb4e from=translated src=- shape=52e44ca1 vocab=001bc621
-/
theorem tendsto_fixedRankNatUpperY_atTop (J : ℕ) (hJ : 0 < J) :
    Tendsto (fixedRankNatUpperY J) atTop atTop := by
  have hreal : Tendsto (fun x : ℕ ↦ fixedRankUpperY J (x : ℝ)) atTop atTop :=
    (tendsto_fixedRankUpperY_atTop J hJ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_nat_floor_atTop.comp hreal

/--
@isnad1 id=eventual.1h1v.s4.1e230a01e58e from=translated src=- shape=3a19f38d vocab=0784f315
-/
theorem eventually_three_le_fixedRankNatY (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, 3 ≤ fixedRankNatY J x :=
  (tendsto_fixedRankNatY_atTop J hJ).eventually_ge_atTop 3

/--
@isnad1 id=eventual.1h1v.s4.9e7cecead1c9 from=translated src=- shape=3a19f38d vocab=52d3bc88
-/
theorem eventually_three_le_fixedRankNatUpperY (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, 3 ≤ fixedRankNatUpperY J x :=
  (tendsto_fixedRankNatUpperY_atTop J hJ).eventually_ge_atTop 3

/--
@isnad1 id=eventual.1h1v.s4.6ca87a3c9434 from=translated src=- shape=42c199ab vocab=652785ad
-/
theorem eventually_fixedRankNatY_le_upperY (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatY J x ≤ fixedRankNatUpperY J x := by
  have hT : ∀ᶠ x : ℕ in atTop, 0 ≤ fixedRankT J (x : ℝ) :=
    ((tendsto_fixedRankT_atTop J hJ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 0
  filter_upwards [hT] with x hx
  exact fixedRankNatY_le_upperY hJ hx

/-! ## The fixed-rank error scale -/

/-- In the positive range, `V/G = 1/A`.
@isnad1 id=eq.2h1v.s5.f8beeb0724b2 from=translated src=- shape=b893f696 vocab=4083f7e4
-/
theorem scaleV_div_scaleG_eq_inv_scaleA {x : ℝ}
    (hL : 0 < scaleL x) (hA : 0 < scaleA x) :
    scaleV x / scaleG x = (scaleA x)⁻¹ := by
  have hG : 0 < scaleG x := scaleG_pos hL hA
  have hsq : scaleG x ^ 2 = scaleL x * scaleA x :=
    scaleG_sq hL.le hA.le
  rw [scaleV_eq]
  field_simp [hG.ne', hA.ne']
  nlinarith

/-- The ratio `V/G` tends to zero.
@isnad1 id=tendsto.0h0v.s5.c0d6e1317f69 from=translated src=- shape=93a4dec3 vocab=a8144619
-/
theorem tendsto_scaleV_div_scaleG_zero :
    Tendsto (fun x ↦ scaleV x / scaleG x) atTop (nhds 0) := by
  have hinv : Tendsto (fun x ↦ (scaleA x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_scaleA_atTop
  apply hinv.congr'
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  exact (scaleV_div_scaleG_eq_inv_scaleA hL hA).symm

/-- The fixed-rank secondary scale satisfies the paper's `V=o(G)`.
@isnad1 id=islittle.0h0v.s3.6e021575354b from=translated src=- shape=47806ae7 vocab=a78438cf
-/
theorem scaleV_isLittleO_scaleG : scaleV =o[atTop] scaleG := by
  refine Asymptotics.isLittleO_of_tendsto' ?_ tendsto_scaleV_div_scaleG_zero
  filter_upwards [eventually_scaleL_pos, eventually_scaleA_pos] with x hL hA
  intro hzero
  exact ((scaleG_pos hL hA).ne' hzero).elim

/-- Any fixed multiple of `V` is still negligible compared with `G`.
@isnad1 id=islittle.0h1v.s4.02d6584a090f from=translated src=- shape=4c790d86 vocab=90fcbd14
-/
theorem const_mul_scaleV_isLittleO_scaleG (c : ℝ) :
    (fun x ↦ c * scaleV x) =o[atTop] scaleG :=
  scaleV_isLittleO_scaleG.const_mul_left c

/-- A positive fixed margin in the main exponent eventually absorbs any fixed multiple of `V`.
@isnad1 id=eventual.1h2v.s5.48bd787f6033 from=translated src=- shape=9f4c3e64 vocab=3a185940
-/
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
