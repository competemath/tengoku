import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.ThreeGeometric
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv
import Tengoku.Seed.Analysis.Calculus.Deriv.Pow
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Analysis.Calculus.Deriv.Add
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar
namespace AdmissibleParams

variable (P : AdmissibleParams)

def chartN : Nat := P.m - 2

def chartU : Real := 1 - P.tau

def chartSigma : Real := P.p / P.alpha

def chartV : Real := P.chartSigma - 1

def chartZeta : Real := P.ell ^ 2 / P.chartU

def chartD : Real := 1 + P.tau ^ 2 + P.ell ^ 2

def chartH : Real := P.chartZeta + 1 + P.chartV

theorem alpha_mul_tau : P.alpha * P.tau = P.q := by
  unfold tau
  field_simp [P.alpha_pos.ne']

theorem alpha_mul_ell : P.alpha * P.ell = P.L := by
  unfold ell
  field_simp [P.alpha_pos.ne']

theorem tau_pos : 0 < P.tau := div_pos P.q_pos P.alpha_pos

theorem tau_lt_one : P.tau < 1 := (div_lt_one P.alpha_pos).2 P.alpha_gt_q

theorem chartU_pos : 0 < P.chartU := by
  unfold chartU; linarith [P.tau_lt_one]

theorem L_pos : 0 < P.L := by
  have hpos : 0 < P.p * P.q - P.alpha ^ 2 := by
    have hquad := P.leading_eigenvalue_quadratic_nonpos
    have hp : P.p = 1 - P.q := rfl
    nlinarith [P.q_pos, P.alpha_gt_q, mul_pos P.q_pos (sub_pos.mpr P.alpha_gt_q)]
  unfold L
  rwa [Real.sqrt_pos]

theorem ell_pos : 0 < P.ell := div_pos P.L_pos P.alpha_pos

theorem chartD_pos : 0 < P.chartD := by
  unfold chartD; positivity

theorem chartSigma_pos : 0 < P.chartSigma := div_pos P.p_pos P.alpha_pos

theorem chartSigma_gt_one : 1 < P.chartSigma :=
  (one_lt_div P.alpha_pos).2 P.alpha_lt_p

theorem chartV_pos : 0 < P.chartV := by
  unfold chartV; linarith [P.chartSigma_gt_one]

theorem chartZeta_pos : 0 < P.chartZeta :=
  div_pos (pow_pos P.ell_pos 2) P.chartU_pos

theorem chartD_mul_alpha_sq : P.alpha ^ 2 * P.chartD = P.q := by
  have ht2 : P.alpha ^ 2 * P.tau ^ 2 = P.q ^ 2 := by
    rw [← P.alpha_mul_tau]; ring
  have hl2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by
    rw [← P.alpha_mul_ell]; ring
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hp : P.p = 1 - P.q := rfl
  unfold chartD
  linear_combination ht2 + hl2 + hL + P.q * hp

theorem chartD_mul_q : P.q * P.chartD = P.tau ^ 2 := by
  have hmaster := P.chartD_mul_alpha_sq
  have htau2 : P.tau ^ 2 * P.alpha ^ 2 = P.q ^ 2 := by
    rw [← P.alpha_mul_tau]; ring
  have h1 : P.q * P.chartD * P.alpha ^ 2 = P.tau ^ 2 * P.alpha ^ 2 := by
    have e : P.q * P.chartD * P.alpha ^ 2 = P.q * (P.alpha ^ 2 * P.chartD) := by ring
    rw [e, hmaster, htau2]; ring
  exact mul_right_cancel₀ (pow_ne_zero 2 P.alpha_pos.ne') h1

theorem chartSigma_mul_tau : P.chartSigma * P.tau = 1 + P.ell ^ 2 := by
  have hl2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by
    rw [← P.alpha_mul_ell]; ring
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hst : P.chartSigma * P.alpha = P.p := by
    unfold chartSigma; field_simp [P.alpha_pos.ne']
  have hta : P.tau * P.alpha = P.q := by
    rw [mul_comm]; exact P.alpha_mul_tau
  have h1 : P.chartSigma * P.tau * P.alpha ^ 2 = (1 + P.ell ^ 2) * P.alpha ^ 2 := by
    have e : P.chartSigma * P.tau * P.alpha ^ 2
        = (P.chartSigma * P.alpha) * (P.tau * P.alpha) := by ring
    rw [e, hst, hta]
    linear_combination -hl2 - hL
  exact mul_right_cancel₀ (pow_ne_zero 2 P.alpha_pos.ne') h1

theorem ell_lt_tau : P.ell < P.tau := by
  unfold ell tau
  exact (div_lt_div_iff_of_pos_right P.alpha_pos).2 P.L_lt_q

theorem chartD_lt_three_tau_sq : P.chartD < 3 * P.tau ^ 2 := by
  have hqD : P.q * P.chartD = P.tau ^ 2 := P.chartD_mul_q
  have hDpos := P.chartD_pos
  nlinarith [P.q_gt_third, hDpos, hqD,
    mul_pos hDpos (show (0:ℝ) < 3 * P.q - 1 by linarith [P.q_gt_third])]

theorem tau_mul_chartU_le_ell_sq : P.tau * P.chartU ≤ P.ell ^ 2 := by
  have hquad := P.leading_eigenvalue_quadratic_nonpos
  have hl2 : P.alpha ^ 2 * P.ell ^ 2 = P.L ^ 2 := by rw [← P.alpha_mul_ell]; ring
  have hL : P.L ^ 2 = P.p * P.q - P.alpha ^ 2 := P.L_sq
  have hp : P.p = 1 - P.q := rfl
  have hau : P.alpha ^ 2 * (P.tau * P.chartU) = P.q * (P.alpha - P.q) := by
    unfold chartU
    have h1 : P.alpha ^ 2 * P.tau = P.alpha * P.q := by rw [← P.alpha_mul_tau]; ring
    have h2 : P.alpha ^ 2 * P.tau ^ 2 = P.q ^ 2 := by rw [← P.alpha_mul_tau]; ring
    linear_combination h1 - h2
  have hkey : P.alpha ^ 2 * (P.tau * P.chartU) ≤ P.alpha ^ 2 * P.ell ^ 2 := by
    rw [hau, hl2, hL, hp]; nlinarith [hquad]
  exact le_of_mul_le_mul_left hkey (pow_pos P.alpha_pos 2)

theorem tau_gt_three_quarters : 3 / 4 < P.tau := by
  have hDge : 1 + P.tau ≤ P.chartD := by
    have hu : P.chartU = 1 - P.tau := rfl
    have h := P.tau_mul_chartU_le_ell_sq
    rw [hu] at h
    unfold chartD
    nlinarith [h]
  have h3 : 1 + P.tau < 3 * P.tau ^ 2 := lt_of_le_of_lt hDge P.chartD_lt_three_tau_sq
  have ha23 : (2:ℝ) / 3 < P.tau := by
    show (2:ℝ) / 3 < P.q / P.alpha
    rw [lt_div_iff₀ P.alpha_pos]
    nlinarith [P.q_gt_third, P.alpha_lt_half]
  nlinarith [h3, ha23, P.tau_pos]

theorem chartSigma_lt_two : P.chartSigma < 2 := by
  show P.p / P.alpha < 2
  rw [div_lt_iff₀ P.alpha_pos]
  have hp : P.p < 2 / 3 := by have := P.q_gt_third; unfold p; linarith
  have hα : 1 / 3 < P.alpha := P.q_gt_third.trans P.alpha_gt_q
  linarith

theorem chartV_lt_one : P.chartV < 1 := by
  unfold chartV; linarith [P.chartSigma_lt_two]

theorem chartZeta_mul_chartU : P.chartZeta * P.chartU = P.ell ^ 2 := by
  unfold chartZeta
  field_simp [P.chartU_pos.ne']

theorem tau_mul_chartH : P.tau * P.chartH = 1 + P.chartZeta := by
  have hA : P.tau * P.chartV + P.tau = 1 + P.ell ^ 2 := by
    have h := P.chartSigma_mul_tau
    have hv : P.chartSigma = P.chartV + 1 := by unfold chartV; ring
    rw [hv] at h
    linear_combination h
  have hB : P.chartZeta - P.chartZeta * P.tau = P.ell ^ 2 := by
    have h := P.chartZeta_mul_chartU
    have hu : P.chartU = 1 - P.tau := rfl
    rw [hu] at h
    linear_combination h
  unfold chartH
  linear_combination hA - hB

theorem chartU_mul_chartH : P.chartU * P.chartH = P.chartV := by
  have ha := P.tau_mul_chartH
  have hu : P.chartU = 1 - P.tau := rfl
  unfold chartH at ha ⊢
  rw [hu]
  linear_combination -ha

theorem chartH_pos : 0 < P.chartH := by
  unfold chartH; linarith [P.chartZeta_pos, P.chartV_pos]

def chartFN : Real :=
  1 - P.tau ^ P.chartN - P.ell ^ 2 * (P.tau ^ P.chartN - P.ell ^ P.chartN)

def chartTN : Real :=
  (P.chartN : Real) - P.chartZeta * (P.tau ^ P.chartN - P.ell ^ P.chartN)

def chartKA : Real := (P.chartSigma ^ (P.chartN + 1) - 1) / (P.chartSigma + 1)

def chartKL : Real :=
  (P.chartSigma ^ (P.chartN + 1) - P.ell ^ (P.chartN + 1)) / (P.chartSigma + P.ell)

theorem chartN_pos_real : (0:ℝ) < (P.chartN : Real) := by
  have : 0 < P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  exact_mod_cast this

theorem tau_sub_ell_gt_chartU : P.chartU < P.tau - P.ell := by
  have hDlt := P.chartD_lt_three_tau_sq
  have hDeq : P.chartD = 1 + P.tau ^ 2 + P.ell ^ 2 := rfl
  have hell2 : P.ell ^ 2 < 2 * P.tau ^ 2 - 1 := by rw [hDeq] at hDlt; linarith
  have hlt : P.ell ^ 2 < (2 * P.tau - 1) ^ 2 := by nlinarith [sq_nonneg (P.tau - 1)]
  have h2a1 : 0 < 2 * P.tau - 1 := by linarith [P.tau_gt_three_quarters]
  have hell_lt : P.ell < 2 * P.tau - 1 := by
    by_contra hcon
    have hge : 2 * P.tau - 1 ≤ P.ell := not_lt.mp hcon
    nlinarith [hlt, hge, h2a1, P.ell_pos]
  unfold chartU
  linarith [hell_lt]

def chartR : Nat := (P.chartN + 1) / 2

theorem two_mul_chartR : 2 * P.chartR = P.chartN + 1 := by
  obtain ⟨k, hk⟩ := P.m_odd
  have := P.m_ge_nine
  unfold chartR chartN
  omega

def chartZ : Real :=
  (P.chartN : Real) * (1 + P.chartV) / (1 - (Real.sqrt P.chartV) ^ P.chartN)

theorem chartR_pos : 1 ≤ P.chartR := by
  have h1 := P.two_mul_chartR
  have h2 : 7 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  omega

def chartOmega : Real :=
  (P.chartN : Real) * P.chartV / ((P.chartN : Real) + 1 - (Real.sqrt P.chartV) ^ P.chartN)

end AdmissibleParams
end OddCycleBound.IntermediateRegion.Scalar
