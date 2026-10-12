import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.CapBounds

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.CapNumeric
open Real Set
noncomputable def Q (t:ℝ) := (4/15:ℝ)-t/35-t^2/504
noncomputable def U (t:ℝ) := (1-t)*t^2*Real.sqrt (2*t)*Q t
noncomputable def R (t:ℝ) := (4/3:ℝ)-31*t/15+67*t^2/280+11*t^3/504

lemma hasDerivAt_Q (t:ℝ) : HasDerivAt Q (-1/35-2*t/504) t := by
  unfold Q
  convert (((hasDerivAt_id t).div_const 35).const_sub (4/15) |>.sub
    (((hasDerivAt_id t).pow 2).div_const 504)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
lemma hasDerivAt_R (t:ℝ) : HasDerivAt R (-31/15+67*t/140+11*t^2/168) t := by
  unfold R
  convert ((((hasDerivAt_id t).const_mul 31).div_const 15).const_sub (4/3) |>.add
    ((((hasDerivAt_id t).pow 2).const_mul 67).div_const 280) |>.add
    ((((hasDerivAt_id t).pow 3).const_mul 11).div_const 504)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
lemma hasDerivAt_U {t:ℝ} (ht:0<t) : HasDerivAt U (Real.sqrt (2*t)*t/2*R t) t := by
  have hs : 0<Real.sqrt (2*t) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*t by positivity)
  unfold U
  convert ((((hasDerivAt_id t).const_sub 1).mul ((hasDerivAt_id t).pow 2)).mul
    (((hasDerivAt_id t).const_mul 2).sqrt (by positivity)) |>.mul (hasDerivAt_Q t)) using 1 <;> first | rfl | (dsimp [Q,R]; field_simp; rw [hsq]; ring)

lemma Q_nonneg {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : 0≤Q t := by
  have hsq : t^2≤1 := by nlinarith only [ht.1,ht.2]
  unfold Q; linarith only [ht.2,hsq]
lemma Q_antitone : AntitoneOn Q (Icc (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold Q; fun_prop)
    (fun t ht=>(hasDerivAt_Q t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_Q t).deriv]
  rw [interior_Icc] at ht
  linarith only [ht.1]
lemma R_antitone : AntitoneOn R (Icc (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold R; fun_prop)
    (fun t ht=>(hasDerivAt_R t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_R t).deriv]
  rw [interior_Icc] at ht
  have hsq : t^2≤1 := by nlinarith only [ht.1,ht.2]
  linarith only [ht.2,hsq]

lemma U_middle {t:ℝ} (ht:t∈Icc (7067/10000:ℝ) (7068/10000:ℝ)) : U t < (428/10000:ℝ) := by
  have ht0 : 0≤t := by linarith only [ht.1]
  have ht1 : t≤1 := by linarith only [ht.2]
  have hq : Q t≤Q (7067/10000) := Q_antitone (by norm_num) ⟨ht0,ht1⟩ ht.1
  have hs : Real.sqrt (2*t)≤1189/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [ht.2]⟩
  have ht2 : t^2≤(7068/10000:ℝ)^2 := (sq_le_sq₀ ht0 (by norm_num)).mpr ht.2
  have hp := mul_le_mul (show 1-t≤2933/10000 by linarith only [ht.1]) ht2 (sq_nonneg t) (by norm_num)
  have hp' := mul_le_mul hp hs (Real.sqrt_nonneg _) (by norm_num)
  have hp'' := mul_le_mul hp' hq (Q_nonneg ⟨ht0,ht1⟩) (by norm_num)
  dsimp [U]
  exact hp''.trans_lt (by norm_num [Q])

lemma U_bound {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : U t < (428/10000:ℝ) := by
  have hl : MonotoneOn U (Icc (0:ℝ) (7067/10000)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by unfold U Q; fun_prop)
      (fun x hx=>(hasDerivAt_U (by rw [interior_Icc] at hx; exact hx.1)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_U hx.1).deriv]
    have hR := R_antitone ⟨hx.1.le,by linarith only [hx.2]⟩ (by norm_num) hx.2.le
    have hpos : 0≤R (7067/10000) := by norm_num [R]
    exact mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hx.1.le) (by norm_num)) (hpos.trans hR)
  have hu : AntitoneOn U (Icc (7068/10000:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold U Q; fun_prop)
      (fun x hx=>(hasDerivAt_U (by rw [interior_Icc] at hx; linarith only [hx.1])).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := by linarith only [hx.1]
    rw [(hasDerivAt_U hx0).deriv]
    have hR := R_antitone (by norm_num) ⟨hx0.le,hx.2.le⟩ hx.1.le
    have hneg : R (7068/10000)≤0 := by norm_num [R]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hR.trans hneg)
  by_cases htl : t≤7067/10000
  · exact (hl ⟨ht.1,htl⟩ (by norm_num) htl).trans_lt (U_middle (by norm_num))
  by_cases htu : 7068/10000≤t
  · exact (hu (by norm_num) ⟨htu,ht.2⟩ htu).trans_lt (U_middle (by norm_num))
  exact U_middle ⟨(lt_of_not_ge htl).le,(lt_of_not_ge htu).le⟩

end GaussianPropeller.CapNumeric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

lemma integral_u_sqrt {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    (∫ u in b..1, u*Real.sqrt (1-u^2)) = (1-b^2)*Real.sqrt (1-b^2)/3 := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.2
    (f:=fun u:ℝ=>-(1-u^2)*Real.sqrt (1-u^2)/3)
    (f':=fun u:ℝ=>u*Real.sqrt (1-u^2)) (by fun_prop) (fun u hu=>?_)
    (by exact (by fun_prop : Continuous (fun u:ℝ=>u*Real.sqrt (1-u^2))).intervalIntegrable _ _)
  · simp only [one_pow,sub_self,neg_zero,zero_mul,zero_div,zero_sub] at hh
    rw [hh]; ring
  have hu0 : 0≤u := hb.1.trans hu.1.le
  have hsq : u^2<1 := by nlinarith only [hu0,hu.2]
  have hp : 0<Real.sqrt (1-u^2) := by positivity
  have hs := Real.sq_sqrt (show 0≤1-u^2 by linarith only [hsq])
  have hd := ((hasDerivAt_id u).pow 2).const_sub 1
  convert ((hd.neg.mul (hd.sqrt (by change 1-u^2≠0; linarith only [hsq]))).div_const 3) using 1 <;> first | rfl | (dsimp; field_simp; rw [hs]; ring)

noncomputable def sphereGap (b:ℝ) := ∫ u in b..1, (u-b)*Real.sqrt (1-u^2)

lemma sphereGap_eq {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    sphereGap b = (1-b^2)*Real.sqrt (1-b^2)/3-b*sphereTail b := by
  have he : (fun u:ℝ => (u-b)*Real.sqrt (1-u^2)) =
      fun u=> u*Real.sqrt (1-u^2)-b*Real.sqrt (1-u^2) := by funext u; ring
  rw [sphereGap,he,intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun u:ℝ=>u*Real.sqrt (1-u^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u:ℝ=>b*Real.sqrt (1-u^2))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,integral_u_sqrt hb]
  rfl

lemma sqrt_two_upper {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    Real.sqrt (2*s-s^2) ≤ Real.sqrt (2*s)*(1-s/4-s^2/32) := by
  have hs2 : s^2≤1 := by nlinarith only [hs.1,hs.2]
  have hp : 0≤1-s/4-s^2/32 := by linarith only [hs.2,hs2]
  have ha : 0≤2*s-s^2 := by nlinarith only [hs.1,hs.2]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hp)).mp
  rw [mul_pow,Real.sq_sqrt ha,Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hs.1)]
  have he : 2*s*(1-s/4-s^2/32)^2-(2*s-s^2) = s^4/32+s^5/512 := by ring
  nlinarith only [he,pow_nonneg hs.1 4,pow_nonneg hs.1 5]

lemma hasDerivAt_sqrt_two {s:ℝ} (hs:0<s) : HasDerivAt (fun s:ℝ=>Real.sqrt (2*s))
    (Real.sqrt (2*s)/(2*s)) s := by
  have hp : 0<Real.sqrt (2*s) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*s by positivity)
  convert (((hasDerivAt_id s).const_mul 2).sqrt (by positivity)) using 1 <;> first | rfl | (dsimp; field_simp; nlinarith only [hsq])

noncomputable def gapPrim (t s:ℝ) := Real.sqrt (2*s)*
    (2*t*s/3-(2/5+t/10)*s^2+(1/14-t/112)*s^3+s^4/144)

lemma hasDerivAt_gapPrim (t:ℝ) {s:ℝ} (hs:0<s) : HasDerivAt (gapPrim t)
    ((t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32)) s := by
  unfold gapPrim
  convert (hasDerivAt_sqrt_two hs).mul
    (((((hasDerivAt_id s).const_mul (2*t)).div_const 3).sub
      (((hasDerivAt_id s).pow 2).const_mul (2/5+t/10))).add
      (((hasDerivAt_id s).pow 3).const_mul (1/14-t/112)) |>.add
      (((hasDerivAt_id s).pow 4).div_const 144)) using 1 <;> first | rfl | (dsimp; field_simp; ring)

lemma sphereGap_upper {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    b*sphereGap b ≤ U (1-b) := by
  let t := 1-b
  have ht : t∈Icc (0:ℝ) 1 := ⟨by dsimp [t]; linarith only [hb.2],by dsimp [t]; linarith only [hb.1]⟩
  have hsub := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=t)
    (fun u:ℝ=>(u-b)*Real.sqrt (1-u^2)) 1
  have he : (fun s:ℝ=>(1-s-b)*Real.sqrt (1-(1-s)^2)) =
      fun s=>(t-s)*Real.sqrt (2*s-s^2) := by funext s; dsimp [t]; rw [show 1-(1-s)^2=2*s-s^2 by ring]; ring
  rw [he,show 1-t=b by dsimp [t]; ring,sub_zero] at hsub
  have hi := intervalIntegral.integral_mono_on (μ:=volume) ht.1
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s-s^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32))).intervalIntegrable _ _)
    (fun s hs=>show (t-s)*Real.sqrt (2*s-s^2)≤(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32) from by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sqrt_two_upper ⟨hs.1,hs.2.trans ht.2⟩) (sub_nonneg.mpr hs.2))
  have hj := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (f:=gapPrim t) (by unfold gapPrim; fun_prop)
    (fun s hs=>hasDerivAt_gapPrim t hs.1)
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32))).intervalIntegrable _ _)
  rw [hsub,hj,show gapPrim t 0=0 by simp [gapPrim],sub_zero] at hi
  have hh := mul_le_mul_of_nonneg_left hi hb.1
  change b*sphereGap b≤_ at hh
  convert hh using 1
  dsimp [gapPrim,U,CapNumeric.Q,t]
  ring

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

end GaussianPropeller.Cap

end OAI
