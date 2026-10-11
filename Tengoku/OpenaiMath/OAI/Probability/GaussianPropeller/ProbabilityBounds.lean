import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.Taylor

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor
noncomputable def p (x : ℝ) : ℝ := gaussianConst*tail x

lemma gaussianConst_tight : (398942/1000000:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  refine ⟨?_, gaussianConst_bounds.2⟩
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
  have hh := Real.pi_lt_d6
  nlinarith

lemma p_pos (x : ℝ) : 0 < p x :=
  mul_pos (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1) (tail_pos x)

lemma p_taylor_lower {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n) x) :
    1/2-(398943/1000000:ℝ)*J (2*n) x ≤ p x := by
  have hh := (integral_exp_bounds n hx).2
  change (∫ t in (0:ℝ)..x, density t) ≤ J (2*n) x at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.2 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma p_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n+1) x) :
    p x ≤ 1/2-(398942/1000000:ℝ)*J (2*n+1) x := by
  have hh := (integral_exp_bounds n hx).1
  change J (2*n+1) x ≤ ∫ t in (0:ℝ)..x, density t at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.1 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma lambda_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hJ : 0 ≤ J (2*n) x)
    (hc : (398943/1000000:ℝ)*E (2*n) (x^2/2) ≤
      L*(1/2-(398943/1000000:ℝ)*J (2*n) x)) : lambda x ≤ L := by
  have he := exp_le_E_even n (show 0 ≤ x^2/2 by positivity)
  rw [← neg_div] at he
  change density x ≤ E (2*n) (x^2/2) at he
  have hd : 0 ≤ density x := (Real.exp_pos _).le
  have hmul := mul_le_mul he gaussianConst_tight.2
    (le_trans (by norm_num) gaussianConst_tight.1) (hd.trans he)
  have ht := mul_le_mul_of_nonneg_left (p_taylor_lower hx n hJ) hL
  have hpos : 0 < gaussianConst := lt_of_lt_of_le (by norm_num) gaussianConst_tight.1
  rw [lambda, div_le_iff₀ (tail_pos x)]
  apply (mul_le_mul_iff_right₀ hpos).mp
  dsimp [p] at ht
  nlinarith only [hmul,hc,ht]

noncomputable def loss (x : ℝ) : ℝ := p x^2*G x

lemma loss_eq (x : ℝ) : loss x=gaussianConst^2*density x*(density x-x*tail x) := by
  unfold loss p G lambda
  field_simp [(tail_pos x).ne']

lemma row_margin {a b r x U S : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hrb : r ≤ b)
    (hb : b ≤ 2/3) (hU : 0 ≤ U) (hG : G x ≤ U) (hS : 0 ≤ S)
    (hSsq : 1-a^2 ≤ S^2)
    (hc : U*(0.415+0.15*b)^2 < (9/(8*3.1416:ℝ))/(1+S)) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  have hr : 0 ≤ r := ha.trans har
  have hr2 : r^2 ≤ (1:ℝ) := by nlinarith only [hr,hrb,hb]
  have hs := Real.sq_sqrt (show 0 ≤ 1-r^2 by linarith only [hr2])
  have hsp := Real.sqrt_nonneg (1-r^2)
  have hsq : Real.sqrt (1-r^2) ≤ S := by
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by positivity)
    nlinarith only [hs,hsp,hSsq,hS,hm]
  have hbcoef : (0.415+0.15*r)^2 ≤ (0.415+0.15*b)^2 := by
    nlinarith only [hr,hrb, sq_nonneg (b-r)]
  have hh₁ := mul_le_mul_of_nonneg_left hG (sq_nonneg (0.415+0.15*r))
  have hh₂ := mul_le_mul_of_nonneg_right hbcoef hU
  have hB : (9/(8*3.1416:ℝ)) ≤ 9/(8*Real.pi) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [Real.pi_lt_d4])
  have hd₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 9/(8*3.1416))
    (show 0 < 1+Real.sqrt (1-r^2) by positivity) (show 1+Real.sqrt (1-r^2) ≤ 1+S by linarith only [hsq])
  have hd₂ := div_le_div_of_nonneg_right hB (show 0 ≤ 1+Real.sqrt (1-r^2) by positivity)
  have hc' : (0.415+0.15*b)^2*U < (9/(8*3.1416:ℝ))/(1+S) := by simpa only [mul_comm] using hc
  exact lt_of_le_of_lt (hh₁.trans hh₂) (lt_of_lt_of_le hc' (hd₁.trans hd₂))

end GaussianPropeller.ProbabilityBounds

end OAI
