import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SiegelFunction
import Tengoku.FltAnthropic.Theorems.Thm_jacobiTheta_two_eq_tprod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_siegelFun_specialLinearGroup_smul

set_option autoImplicit false

noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace SiegelSL2

def qq (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

def qa (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := cexp (2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ))

def pref (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * τ)

def sprod (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  (1 - qa N r s τ) * ∏' n : ℕ, ((1 - qq τ ^ (n + 1) * qa N r s τ) *
    (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹))

/--
@isnad1 id=eq.0h4v.s5.a7639febb636 from=translated src=- shape=6b4addea vocab=5aa9c4dc
-/
theorem siegelFun_eq (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * sprod N r s τ := by
  unfold ModularCurve.siegelFun pref sprod qq qa; simp only [mul_assoc]

/--
@isnad1 id=eq.0h3v.s4.152aee1f1c10 from=translated src=- shape=e59f7ef4 vocab=51dfd744
-/
theorem siegelFun_level_zero (r s : ℤ) (τ : ℂ) : ModularCurve.siegelFun 0 r s τ = 0 := by
  simp [ModularCurve.siegelFun]

/--
@isnad1 id=eq.0h1v.s4.ca30f88a3328 from=translated src=- shape=3150584f vocab=aa29117c
-/
theorem qq_add_one (τ : ℂ) : qq (τ + 1) = qq τ := by
  unfold qq
  rw [show 2 * π * I * (τ + 1) = 2 * π * I * τ + 2 * π * I by ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

/--
@isnad1 id=eq.0h4v.s5.c1ab155e3c9a from=translated src=- shape=94240339 vocab=42031886
-/
theorem qa_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s (τ + 1) = qa N r (r + s) τ := by
  unfold qa
  push_cast
  ring_nf

/--
@isnad1 id=eq.1h4v.s6.cfe162b0f266 from=translated src=- shape=e45417ba vocab=8b76b549
-/
theorem pref_add_one (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) :
    pref N r s (τ + 1) = cexp (π * I / 6) * pref N r (r + s) τ := by
  unfold pref
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [neg_mul, neg_mul, mul_neg, neg_inj, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.0h4v.s5.499bdee654ae from=translated src=- shape=94240339 vocab=a89e8a18
-/
theorem sprod_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) : sprod N r s (τ + 1) = sprod N r (r + s) τ := by
  unfold sprod
  rw [qq_add_one, qa_add_one]

/--
@isnad1 id=eq.0h4v.s6.d4ee651b76fa from=translated src=- shape=22007c4e vocab=36026704
-/
theorem siegelFun_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s (τ + 1) = cexp (π * I / 6) * ModularCurve.siegelFun N r (r + s) τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelFun_level_zero]
  rw [siegelFun_eq, siegelFun_eq, pref_add_one N hN, sprod_add_one, mul_assoc]

/--
@isnad1 id=lt.1h1v.s4.1404d216821e from=translated src=- shape=57faaa14 vocab=5b642903
-/
theorem norm_qq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qq τ‖ < 1 := by
  unfold qq
  rw [Complex.norm_exp]
  have : (2 * π * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

def P (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - qq τ ^ (n + 1))

/--
@isnad1 id=multipli.1h1v.s6.75ee1a8c4cf3 from=translated src=- shape=1c50effb vocab=b81e0a63
-/
theorem multipliable_P {τ : ℂ} (hτ : 0 < τ.im) : Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow (norm_qq_lt_one hτ)

/--
@isnad1 id=multipli.1h3v.s6.0f0a42d99f48 from=translated src=- shape=5e5b2675 vocab=b137e65d
-/
theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k : ℕ) :
    Multipliable fun n : ℕ => 1 - q ^ (n + k) * c := by
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + k) * c)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_add]
    have := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right (‖q‖ ^ k * ‖c‖)
    refine this.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/--
@isnad1 id=multipli.1h4v.s6.8223876c957d from=translated src=- shape=966906a6 vocab=87b703ef
-/
theorem multipliable_b {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ n * qa N r s τ := by
  simpa using multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 0

/--
@isnad1 id=multipli.1h4v.s6.63759c1f9610 from=translated src=- shape=4e97db60 vocab=484ce99c
-/
theorem multipliable_b_succ {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * qa N r s τ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 1

/--
@isnad1 id=multipli.1h4v.s6.4c670707384d from=translated src=- shape=81213acc vocab=2df65ecd
-/
theorem multipliable_c {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ)⁻¹ 1

def w (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + (1 - τ) / 2

/--
@isnad1 id=eq.1h5v.s8.ab1ed6b4c41a from=translated src=- shape=5c412ca3 vocab=fa42382f
-/
theorem jtp_term (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) (n : ℕ) :
    (1 - cexp (2 * π * I * (n + 1) * τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ)) =
      (1 - qq τ ^ (n + 1)) * ((1 - qq τ ^ n * qa N r s τ) *
        (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e1 : cexp (2 * π * I * (n + 1) * τ) = qq τ ^ (n + 1) := by
    rw [show 2 * π * I * (n + 1) * τ = ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) by push_cast; ring,
      Complex.exp_nat_mul, qq]
  have e2 : cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ) = -(qq τ ^ n * qa N r s τ) := by
    have : π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ =
        (n : ℂ) * (2 * π * I * τ) + 2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + π * I := by
      unfold w; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, qq, qa]
    ring
  have e3 : cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ) =
      -(qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := by
    have : π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ =
        ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) + -(2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ)) +
          -(π * I) := by
      unfold w; push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_neg, Complex.exp_pi_mul_I, qq, qa]
    ring
  rw [e1, e2, e3]; ring

/--
@isnad1 id=eq.2h4v.s5.bc1158fdc605 from=translated src=- shape=eadda7a1 vocab=b76bc0aa
-/
theorem theta_eq (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (w N r s τ) τ = P τ * sprod N r s τ := by
  rw [jacobiTheta_two_eq_tprod _ _ hτ, tprod_congr (jtp_term N hN r s τ)]
  have hP := multipliable_P hτ
  have hb := multipliable_b hτ N r s
  have hb1 := multipliable_b_succ hτ N r s
  have hc := multipliable_c hτ N r s
  have hbc : Multipliable fun n : ℕ => (1 - qq τ ^ n * qa N r s τ) *
      (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := (hb.hasProd.mul hc.hasProd).multipliable
  have h3 : ∏' n : ℕ, (1 - qq τ ^ n * qa N r s τ) =
      (1 - qq τ ^ 0 * qa N r s τ) * ∏' n : ℕ, (1 - qq τ ^ (n + 1) * qa N r s τ) :=
    tprod_eq_zero_mul' hb1
  rw [hP.tprod_mul hbc, hb.tprod_mul hc, h3, pow_zero, one_mul, mul_assoc, ← hb1.tprod_mul hc]
  simp only [P, sprod]

/--
@isnad1 id=eq.0h1v.s5.e34717fa88ed from=translated src=- shape=a23d3c45 vocab=25ae7307
-/
theorem qParam_24 (τ : ℂ) : Function.Periodic.qParam 24 τ = cexp (π * I * τ / 12) := by
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

/--
@isnad1 id=eq.0h2v.s6.114ded6d400c from=translated src=- shape=8103178f vocab=8542d6eb
-/
theorem one_sub_eta_q (n : ℕ) (τ : ℂ) : 1 - ModularForm.eta_q n τ = 1 - qq τ ^ (n + 1) := by
  simp only [ModularForm.eta_q, Function.Periodic.qParam, qq]
  congr 3
  push_cast
  ring

/--
@isnad1 id=eq.0h1v.s5.6b47ae6ab6de from=translated src=- shape=0a45fe5b vocab=b0d4013e
-/
theorem eta_eq (τ : ℂ) : ModularForm.eta τ = cexp (π * I * τ / 12) * P τ := by
  unfold ModularForm.eta P
  rw [qParam_24, tprod_congr (fun n => one_sub_eta_q n τ)]

/--
@isnad1 id=ne.1h1v.s4.a8368f79e254 from=translated src=- shape=555d9df8 vocab=814774e4
-/
theorem P_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : P τ ≠ 0 := by
  have h := ModularForm.eta_tprod_ne_zero (z := τ) hτ
  rwa [tprod_congr (fun n => one_sub_eta_q n τ)] at h

/--
@isnad1 id=eq.1h1v.s6.4bfa0a937194 from=translated src=- shape=eb74fcc6 vocab=d296f926
-/
theorem sqrt_bridge {τ : ℂ} (hτ : 0 < τ.im) :
    (Complex.sqrt I)⁻¹ * Complex.sqrt τ = (-I * τ) ^ (1 / 2 : ℂ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hI : (-I : ℂ) ≠ 0 := by simp
  have hlog : Complex.log (-I * τ) = Complex.log (-I) + Complex.log τ := by
    rw [Complex.log_mul_eq_add_log_iff hI hτ0, Complex.arg_neg_I]
    have h1 : 0 ≤ Complex.arg τ := Complex.arg_nonneg_iff.mpr hτ.le
    have h2 : Complex.arg τ < π := Complex.arg_lt_pi_iff.mpr (Or.inr hτ.ne')
    have hπ := Real.pi_pos
    constructor <;> linarith
  have hcpow : (-I * τ) ^ (1 / 2 : ℂ) = Complex.sqrt (-I) * Complex.sqrt τ := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hI hτ0), hlog, add_mul, Complex.exp_add,
      Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero hI, Complex.cpow_def_of_ne_zero hτ0]
    norm_num
  have hc : ((√(2⁻¹) : ℝ) : ℂ) * ((√(2⁻¹) : ℝ) : ℂ) = 2⁻¹ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast
    ring
  have hprod : Complex.sqrt I * Complex.sqrt (-I) = 1 := by
    rw [Complex.sqrt_I, Complex.sqrt_neg_I]
    calc (((√(2⁻¹) : ℝ) : ℂ) * (1 + I)) * (((√(2⁻¹) : ℝ) : ℂ) * (1 - I))
          = (((√(2⁻¹) : ℝ) : ℂ) * ((√(2⁻¹) : ℝ) : ℂ)) * (1 - I ^ 2) := by ring
      _ = 1 := by rw [hc, Complex.I_sq]; norm_num
  rw [hcpow, inv_eq_of_mul_eq_one_right hprod]

/--
@isnad1 id=eq.0h1v.s6.11670f95e98b from=translated src=- shape=90d141ed vocab=0ab0ddcb
-/
theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * τ) ^ (1 / 2 : ℂ) * ModularForm.eta τ := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [h, ← mul_assoc, sqrt_bridge τ.2]

/--
@isnad1 id=eq.0h1v.s7.b2bc99270d52 from=translated src=- shape=0e8f6afb vocab=352a24c3
-/
theorem P_S (τ : ℍ) :
    P (-1 / (τ : ℂ)) = (-I * τ) ^ (1 / 2 : ℂ) * cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) *
      cexp (π * I * τ / 12) * P τ := by
  have h := eta_S τ
  rw [eta_eq, eta_eq] at h
  have he : cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * cexp (π * I * (-1 / (τ : ℂ)) / 12) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc P (-1 / (τ : ℂ))
        = cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * (cexp (π * I * (-1 / (τ : ℂ)) / 12) * P (-1 / (τ : ℂ))) := by
          rw [← mul_assoc, he, one_mul]
    _ = _ := by rw [h]; ring

/--
@isnad1 id=ne.0h1v.s5.466e0e81ad1a from=translated src=- shape=a1c44286 vocab=f157efac
-/
theorem cpow_half_ne_zero (τ : ℍ) : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero (by simp) τ.ne_zero)

/--
@isnad1 id=eq.1h4v.s8.a43df6551ed5 from=translated src=- shape=99ba1572 vocab=3b8853d4
-/
theorem theta_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    jacobiTheta₂ (w N r s (-1 / (τ : ℂ))) (-1 / (τ : ℂ)) =
      (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * jacobiTheta₂ (w N s (-r) τ) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hA := cpow_half_ne_zero τ
  have hz : (w N s (-r) τ + τ) / τ = w N r s (-1 / (τ : ℂ)) := by
    unfold w; push_cast; field_simp; ring
  symm
  calc (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * jacobiTheta₂ (w N s (-r) τ) τ
        = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            jacobiTheta₂ (w N s (-r) τ + τ) τ := by
          rw [jacobiTheta₂_add_left']; ring
    _ = (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            (1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
              jacobiTheta₂ ((w N s (-r) τ + τ) / τ) (-1 / τ)) := by
          rw [← jacobiTheta₂_functional_equation]
    _ = jacobiTheta₂ ((w N s (-r) τ + τ) / τ) (-1 / τ) := by
          have he : cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
              cexp (-π * I * (w N s (-r) τ + τ) ^ 2 / τ) = 1 := by
            rw [← Complex.exp_add]
            convert Complex.exp_zero using 2
            ring
          calc _ = ((-I * τ) ^ (1 / 2 : ℂ) * (1 / (-I * τ) ^ (1 / 2 : ℂ))) *
                (cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
                  cexp (-π * I * (w N s (-r) τ + τ) ^ 2 / τ)) *
                jacobiTheta₂ ((w N s (-r) τ + τ) / τ) (-1 / τ) := by ring
            _ = _ := by rw [he, mul_one_div_cancel hA, one_mul, one_mul]
    _ = _ := by rw [hz]

/--
@isnad1 id=eq.1h4v.s8.6a63e5366f50 from=translated src=- shape=0953b7cb vocab=656f8b51
-/
theorem sprod_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    sprod N r s (-1 / (τ : ℂ)) =
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) * sprod N s (-r) τ := by
  have hτ' : 0 < (-1 / (τ : ℂ)).im := by
    have : -1 / (τ : ℂ) = (-(τ : ℂ))⁻¹ := by rw [inv_neg, neg_div, one_div]
    rw [this]; exact τ.im_inv_neg_coe_pos
  have h1 := theta_eq N hN r s hτ'
  have h2 := theta_eq N hN s (-r) τ.2
  have h3 := theta_S N hN r s τ
  rw [h1, h2, P_S] at h3

  have hne : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) *
      cexp (π * I * τ / 12) * P τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (cpow_half_ne_zero τ) (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)) (P_ne_zero τ.2)
  refine mul_left_cancel₀ hne ?_
  rw [h3]
  have he : cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * cexp (π * I * τ / 12) *
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) =
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) * cexp (-π * I * (τ + 2 * w N s (-r) τ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * (P τ * sprod N s (-r) τ)
        = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * (cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            cexp (-π * I * (τ + 2 * w N s (-r) τ))) * P τ * sprod N s (-r) τ := by ring
    _ = _ := by rw [← he]; ring

/--
@isnad1 id=eq.1h4v.s8.4c491c6c6f82 from=translated src=- shape=de7f6957 vocab=0e16163f
-/
theorem pref_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    pref N r s (-1 / (τ : ℂ)) *
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) = -I * pref N s (-r) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hI : -I = cexp (-(π / 2 * I)) := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  unfold pref
  rw [hI]
  simp only [neg_mul, mul_neg, neg_inj, ← Complex.exp_add]
  congr 1
  unfold w
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.0h4v.s5.a9ba7ee111e1 from=translated src=- shape=55f3bd8e vocab=02b62455
-/
theorem siegelFun_S (N : ℕ) (r s : ℤ) (τ : ℍ) :
    ModularCurve.siegelFun N r s (-1 / (τ : ℂ)) = -I * ModularCurve.siegelFun N s (-r) τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelFun_level_zero]
  rw [siegelFun_eq, siegelFun_eq, sprod_S N hN, ← mul_assoc, pref_S N hN, mul_assoc]

def Law (N : ℕ) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
    ModularCurve.siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
      μ * ModularCurve.siegelFun N
        (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
        (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ)

/--
@isnad1 id=law.0h1v.s6.776f2bb78fd3 from=translated src=- shape=05febd54 vocab=ed30cb8f
-/
theorem law_one (N : ℕ) : Law N 1 :=
  ⟨1, one_pow _, fun r s τ => by simp⟩

/--
@isnad1 id=law.0h1v.s2.6b35f76f3be6 from=translated src=- shape=2d69f17f vocab=f7dbb330
-/
theorem law_T (N : ℕ) : Law N ModularGroup.T := by
  refine ⟨cexp (π * I / 6), ?_, fun r s τ => ?_⟩
  · rw [← Complex.exp_nat_mul]
    convert Complex.exp_two_pi_mul_I using 2
    push_cast; ring
  · rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
    simp only [ModularGroup.coe_T, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    push_cast
    rw [add_comm (1 : ℂ), siegelFun_add_one]
    congr 2 <;> ring

/--
@isnad1 id=law.0h1v.s2.7b68e8e2db42 from=translated src=- shape=2d69f17f vocab=1098c52d
-/
theorem law_S (N : ℕ) : Law N ModularGroup.S := by
  refine ⟨-I, by rw [neg_pow, show (12 : ℕ) = 2 * 6 by rfl, pow_mul, pow_mul, Complex.I_sq]; norm_num,
    fun r s τ => ?_⟩
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  simp only [ModularGroup.coe_S, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  rw [show (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) by rw [inv_neg, neg_div, one_div], siegelFun_S]
  congr 2 <;> ring

/--
@isnad1 id=law.2h3v.s7.0ee21176af61 from=translated src=- shape=f1913286 vocab=eae148b5
-/
theorem law_mul {N : ℕ} {α β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hα : Law N α) (hβ : Law N β) :
    Law N (α * β) := by
  obtain ⟨μ, hμ, hα⟩ := hα
  obtain ⟨ν, hν, hβ⟩ := hβ
  refine ⟨μ * ν, by rw [mul_pow, hμ, hν, one_mul], fun r s τ => ?_⟩
  rw [mul_smul, hα, hβ, mul_assoc]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  congr 3 <;> ring

/--
@isnad1 id=law.1h2v.s6.43c5d4ff03e9 from=translated src=- shape=5054e8db vocab=105c9885
-/
theorem law_inv {N : ℕ} {α : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hα : Law N α) : Law N α⁻¹ := by
  obtain ⟨μ, hμ, hα⟩ := hα
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ
  refine ⟨μ⁻¹, by rw [inv_pow, hμ, inv_one], fun r s τ => ?_⟩
  have hdet : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := α.det_coe
    rwa [Matrix.det_fin_two] at this
  set r' : ℤ := r * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
    s * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hr'
  set s' : ℤ := r * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
    s * ((α⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hs'
  have h := hα r' s' (α⁻¹ • τ)
  rw [smul_inv_smul] at h
  have h1 : r' * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s' * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by
    simp only [hr', hs', Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    linear_combination r * hdet
  have h2 : r' * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s' * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = s := by
    simp only [hr', hs', Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    linear_combination s * hdet
  rw [h1, h2] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]

/--
@isnad1 id=law.0h2v.s4.2ae21b53166f from=translated src=- shape=d97326eb vocab=ed30cb8f
-/
theorem law_all (N : ℕ) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Law N α := by
  have hmem : α ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  refine Subgroup.closure_induction (fun x hx => ?_) (law_one N) (fun x y _ _ hx hy => law_mul hx hy)
    (fun x _ hx => law_inv hx) hmem
  rcases hx with rfl | rfl
  · exact law_S N
  · exact law_T N

end SiegelSL2

open ModularCurve

/--
@isnad1 id=ex.0h2v.s9.c27beedbdf9e from=translated src=- shape=0923d4b7 vocab=fe649354
-/
theorem solution (N : ℕ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * siegelFun N (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ) :=
  SiegelSL2.law_all N α
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
