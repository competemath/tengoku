import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Geometry.Affine

namespace OAI

noncomputable section

namespace SubsphereCurrent.Fixed
section
open scoped ENNReal NNReal

def boundConstant : ℝ := Real.exp 2048
lemma boundConstant_pos : 0 < boundConstant := Real.exp_pos _
lemma two_le_boundConstant : 2 ≤ boundConstant := by
  have h := Real.add_one_le_exp (2048 : ℝ)
  unfold boundConstant
  linarith

lemma parameters {d j m : ℕ} (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) :
    let q := (m-1)/4
    2 ≤ q ∧ d ≤ 16*q ∧ d/32 ≤ q ∧ (d : ℝ)/32 ≤ 2*q ∧
      j*(d/32)/q+1 ≤ j+1 := by
  have hdm : d ≤ 2*m := by
    have : (d : ℝ) ≤ 2*m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  dsimp
  have hq : 2 ≤ (m-1)/4 := by omega
  have hq32 : d/32 ≤ (m-1)/4 := by omega
  refine ⟨hq, by omega, hq32, ?_, ?_⟩
  · have hn : d ≤ 64*((m-1)/4) := by omega
    have hr : (d : ℝ) ≤ 64*((m-1)/4 : ℕ) := by exact_mod_cast hn
    linarith
  · have hmul : j*(d/32) ≤ j*((m-1)/4) := Nat.mul_le_mul_left j hq32
    have hdiv : j*(d/32)/((m-1)/4) ≤ j := by
      exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)
    omega

lemma raw_bound_le {d j m : ℕ} {η : ℝ}
    (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) (hmd : m ≤ d)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ((3 : ℝ)*4^m * η^(2*((m-1)/4))) *
      ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(((m-1)/4 : ℕ) : ℝ)))^
        (j*(d/32)/((m-1)/4)+1) ≤
      (boundConstant^(j+1)*η)^((d : ℝ)/32) := by
  let q := (m-1)/4
  let b := j*(d/32)/q+1
  obtain ⟨hq,hdq,_,ha,hb⟩ := parameters hd hm
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hdp : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hmp : (m : ℝ) ≤ d := by exact_mod_cast hmd
  have hdqp : (d : ℝ) ≤ 16*q := by exact_mod_cast hdq
  have hbp : (b : ℝ) ≤ j+1 := by exact_mod_cast hb
  have hapse : (d : ℝ)/32 ≤ (2*q : ℕ) := by simpa [q] using ha
  have hMq : (d : ℝ)^2/q ≤ 16*d := by
    apply (div_le_iff₀ hqpos).2
    nlinarith [mul_le_mul_of_nonneg_left hdqp (Nat.cast_nonneg d)]
  have hlogη : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog3 : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hlog4 : Real.log (4 : ℝ) ≤ 4 := Real.log_le_self (by norm_num)
  have hlog32 : Real.log (32768 : ℝ) ≤ 15 := by
    have he : (32768 : ℝ) = 2^(15 : ℕ) := by norm_num
    rw [he,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hinside : (m : ℝ)*Real.log 32768 + (d : ℝ)^2/q*Real.log 2 ≤ 31*d := by
    have h1 := mul_le_mul_of_nonneg_left hlog32 (Nat.cast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ (d : ℝ)^2/q)
    nlinarith
  have hfull : (b : ℝ)*((m : ℝ)*Real.log 32768 + (d : ℝ)^2/q*Real.log 2)
      ≤ 31*d*(j+1) := by
    calc
      _ ≤ (b : ℝ)*(31*d) := mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg b)
      _ ≤ ((j : ℝ)+1)*(31*d) := mul_le_mul_of_nonneg_right hbp (by positivity)
      _ = _ := by ring
  have hεpow := mul_le_mul_of_nonpos_right hapse hlogη
  have hrawpos : 0 < ((3 : ℝ)*4^m * η^(2*q)) *
      ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(q : ℝ)))^b := by positivity
  have htargpos : 0 < (boundConstant^(j+1)*η)^((d : ℝ)/32) := by
    exact Real.rpow_pos_of_pos (mul_pos (pow_pos boundConstant_pos _) hη) _
  apply (Real.log_le_log_iff hrawpos htargpos).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_pow,
    Real.log_rpow (by positivity),Real.log_pow,
    Real.log_rpow (mul_pos (pow_pos boundConstant_pos _) hη),
    Real.log_mul (pow_ne_zero _ boundConstant_pos.ne') hη.ne',Real.log_pow]
  have he : (1/(q : ℝ))*((d^2 : ℕ)*Real.log 2) = (d : ℝ)^2/q*Real.log 2 := by
    push_cast; ring
  rw [he]
  simp only [boundConstant, Real.log_exp]
  have h4 := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg m)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hεpow ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hdp) (show (0 : ℝ) ≤ (j:ℝ)+1 by positivity)]

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u

end SubsphereCurrent.Fixed

end

end OAI
