import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Geometry.Affine

namespace OAI

noncomputable section

namespace SubsphereCurrent.Affine
open scoped ENNReal NNReal

lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,Real.log_inv] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

lemma log_thousand_lower : (4 : ℝ) ≤ Real.log 1000 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256) (by norm_num : (256 : ℝ) ≤ 1000)
  rw [show (256 : ℝ) = 2^(8 : ℕ) by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [log_two_bounds.1]

lemma affine_parameters {d n ell : ℕ} (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) :
    let q := (n-1)/4
    2 ≤ q ∧ n ≤ 5*q ∧ d ≤ 2*n ∧ d/16 ≤ q ∧ d/8 ≤ 2*q ∧
      2*(d/32) ≤ 2*q ∧ ell*(d/16)/q+1 ≤ ell+1 := by
  dsimp
  have hq : 2 ≤ (n-1)/4 := by omega
  have hm : d/16 ≤ (n-1)/4 := by omega
  refine ⟨hq,by omega,by omega,hm,by omega,by omega,?_⟩
  have := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left ell hm)
  omega

lemma log_card_of_width {d J : ℕ} {W : ℝ} (hd : 128 ≤ d) (hJ : 1 ≤ J)
    (hJW : (J : ℝ) ≤ W) (hbudget : W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d) :
    Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2 := by
  have hp : (0 : ℝ) < (d/8 : ℕ) := by exact_mod_cast (by omega : 0 < d/8)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hWp : 0 < W := hJp.trans_le hJW
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hWp _) hbudget
  rw [Real.log_rpow hWp,Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have he : ((d/8 : ℕ) : ℝ)*(1/((d/8 : ℕ) : ℝ)*Real.log W) = Real.log W := by
    field_simp
  rw [he] at hmul
  exact (Real.log_le_log hJp hJW).trans (by nlinarith [hmul])

lemma affine_raw_bound {d n ell J : ℕ} {η : ℝ}
    (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) (hell : 1 ≤ ell)
    (hJ : 1 ≤ J)
    (hbudget : Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (hη : 0 < η) (hsmall : 16*((1000 : ℝ)^32)^ell*η ≤ 1) :
    ((3 : ℝ)*4^n * η^(2*((n-1)/4))) *
      ((32768 : ℝ)^n * (J : ℝ)^(1/(((n-1)/4 : ℕ) : ℝ)))^
        (ell*(d/16)/((n-1)/4)+1) ≤
      (16*((1000 : ℝ)^32)^ell*η)^(2*(d/32)) := by
  let q := (n-1)/4
  let a := 2*(d/32)
  let b := ell*(d/16)/q+1
  let c : ℝ := 16*((1000 : ℝ)^32)^ell
  obtain ⟨hq,hnq,hdn,_,hpq,haq,hb⟩ := affine_parameters hd hn
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnr : (n : ℝ) ≤ 5*q := by exact_mod_cast hnq
  have hdr : (d : ℝ) ≤ 2*n := by exact_mod_cast hdn
  have hpr : ((d/8 : ℕ) : ℝ) ≤ 2*q := by exact_mod_cast hpq
  have hbr : (b : ℝ) ≤ ell+1 := by exact_mod_cast hb
  have her : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have har : (a : ℝ) ≤ 2*q := by exact_mod_cast haq
  have hcp : 0 < c := by dsimp [c]; positivity
  have hlogη : Real.log η ≤ -Real.log c := by
    have hl := Real.log_le_log (mul_pos hcp hη) hsmall
    rw [Real.log_mul hcp.ne' hη.ne',Real.log_one] at hl
    linarith
  have hMQ : Real.log (J : ℝ)/q ≤ 2*d := by
    apply (div_le_iff₀ hqp).2
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.2
      (show 0 ≤ ((d/8 : ℕ) : ℝ)*d by positivity)
    have hh' := mul_le_mul_of_nonneg_right hpr (Nat.cast_nonneg d)
    nlinarith
  have hlog32 : Real.log (32768 : ℝ) ≤ 15 := by
    rw [show (32768 : ℝ) = 2^(15 : ℕ) by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_bounds.2]
  have hi : (n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q ≤ 19*n := by
    have := mul_le_mul_of_nonneg_left hlog32 (Nat.cast_nonneg n)
    linarith
  have hfull : (b : ℝ)*((n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q) ≤ 38*n*ell := by
    calc
      _ ≤ (b : ℝ)*(19*n) := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg b)
      _ ≤ ((ell : ℝ)+1)*(19*n) := mul_le_mul_of_nonneg_right hbr (by positivity)
      _ ≤ 38*n*ell := by nlinarith [mul_nonneg (Nat.cast_nonneg n (α := ℝ)) (sub_nonneg.mpr her)]
  have hlogc : 128*(ell : ℝ) ≤ Real.log c := by
    dsimp [c]
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    have := mul_le_mul_of_nonneg_left log_thousand_lower (show 0 ≤ (ell : ℝ)*32 by positivity)
    have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hcost : Real.log 3 + (n : ℝ)*Real.log 4 +
      (b : ℝ)*((n : ℝ)*Real.log 32768 + Real.log (J : ℝ)/q) ≤ 2*q*Real.log c := by
    have h3 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
    have h4 := mul_le_mul_of_nonneg_left (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4))
      (Nat.cast_nonneg n)
    have hqc := mul_le_mul_of_nonneg_left hlogc (show (0 : ℝ) ≤ 2*q by positivity)
    have hnell := mul_le_mul_of_nonneg_right hnr (Nat.cast_nonneg ell)
    have hne : (n : ℝ) ≤ n*ell := by nlinarith
    nlinarith
  have hηcost := mul_le_mul_of_nonneg_left hlogη (sub_nonneg.mpr har)
  apply (Real.log_le_log_iff (by positivity) (by positivity : 0 < (c*η)^a)).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_rpow hJp,
    Real.log_pow,Real.log_mul hcp.ne' hη.ne']
  change Real.log 3 + (n : ℝ)*Real.log 4 + ((2*q : ℕ) : ℝ)*Real.log η +
    (b : ℝ)*((n : ℝ)*Real.log 32768 + (1/(q : ℝ))*Real.log (J : ℝ)) ≤
      (a : ℝ)*(Real.log c+Real.log η)
  rw [show (1/(q : ℝ))*Real.log (J : ℝ) = Real.log (J : ℝ)/q by ring]
  push_cast
  nlinarith

lemma affine_zero_bound {n a : ℕ} {η : ℝ} (hn : 3 ≤ n) (ha : a ≤ n-1)
    (hη : 0 ≤ η) (hsmall : 16*η ≤ 1) :
    (3 : ℝ)*4^n * η^(n-1) ≤ (16*η)^a := by
  have he : n = (n-3)+3 := by omega
  have he' : n-1 = (n-3)+2 := by omega
  have hc : (3 : ℝ)*4^n ≤ 16^(n-1) := by
    calc
      (3 : ℝ)*4^n = 192*4^(n-3) := by
        conv_lhs => rw [he,pow_add]
        norm_num
        ring
      _ ≤ 256*16^(n-3) := by
        have hh : (4 : ℝ)^(n-3) ≤ 16^(n-3) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have h0 : (0 : ℝ) ≤ 4^(n-3) := by positivity
        linarith
      _ = (16 : ℝ)^(n-1) := by rw [he',pow_add]; norm_num; ring
  calc
    _ ≤ 16^(n-1)*η^(n-1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hη _)
    _ = (16*η)^(n-1) := by rw [mul_pow]
    _ ≤ _ := pow_le_pow_of_le_one (by positivity) hsmall ha

end SubsphereCurrent.Affine
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine

end

end OAI
