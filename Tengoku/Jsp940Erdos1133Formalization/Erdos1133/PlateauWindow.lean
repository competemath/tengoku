import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.EntireSinc
import Tengoku.Seed.Analysis.Calculus.ParametricIntervalIntegral
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology Real
open MeasureTheory Set Filter
open Erdos1152.V5

namespace Erdos1133

/-- The sixth-power sinc plateau used to truncate an entire interpolant.-/
def plateauWindow (α τ : ℝ) (z : ℂ) : ℂ :=
  (α : ℂ) * ∫ t : ℝ in -τ..τ, entireSinc ((α : ℂ) * (z - t)) ^ 6

def plateauWindowReal (α τ x : ℝ) : ℝ :=
  α * ∫ t : ℝ in -τ..τ, Real.sinc (α * (x-t)) ^ 6

/--
@isnad1 id=eq.0h3v.s4.2ae5c39384ca from=translated src=- shape=49d2e2cb vocab=4b34b8cd
-/
@[simp] theorem plateauWindow_real (α τ x : ℝ) :
    plateauWindow α τ x = (plateauWindowReal α τ x : ℂ) := by
  unfold plateauWindow plateauWindowReal
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show (α : ℂ) * ((x : ℂ) - t) = ((α * (x-t) : ℝ) : ℂ) by push_cast; rfl,
    entireSinc_real]
  push_cast
  rfl

/--
@isnad1 id=differen.0h2v.s6.deba178aebc2 from=translated src=- shape=feb27325 vocab=13464994
-/
theorem differentiable_plateauWindow (α τ : ℝ) : Differentiable ℂ (plateauWindow α τ) := by
  let F : ℂ → ℝ → ℂ := fun z t => entireSinc ((α : ℂ) * (z-t)) ^ 6
  let F' : ℂ → ℝ → ℂ := fun z t =>
    6 * entireSinc ((α : ℂ) * (z-t)) ^ 5 *
      (deriv entireSinc ((α : ℂ) * (z-t)) * α)
  have hc : Continuous entireSinc := differentiable_entireSinc.continuous
  have hc' : Continuous (deriv entireSinc) := differentiable_entireSinc.deriv.continuous
  have hd (z : ℂ) (t : ℝ) : HasDerivAt (fun w => F w t) (F' z t) z := by
    convert (((differentiable_entireSinc _).hasDerivAt.comp z
        ((hasDerivAt_id z).sub_const (t : ℂ) |>.const_mul (α : ℂ))).pow 6) using 1 <;>
      first | rfl | simp [F']
  have hcF (z : ℂ) : Continuous (F z) := by dsimp [F]; fun_prop
  have hcF' : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by dsimp [F']; fun_prop
  have hi : Differentiable ℂ (fun z => ∫ t : ℝ in -τ..τ, F z t) := by
    intro z
    obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod
      (isCompact_uIcc (a := -τ) (b := τ))).exists_bound_of_continuousOn hcF'.continuousOn
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (s := Metric.closedBall z 1) (bound := fun _ => C)
      (μ := volume) (a := -τ) (b := τ)
      (Metric.closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
      (Eventually.of_forall fun w => (hcF w).aestronglyMeasurable)
      ((hcF z).intervalIntegrable _ _)
      ((hcF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun t ht w hw => hC (w,t) ⟨hw, uIoc_subset_uIcc ht⟩)
      (continuous_const.intervalIntegrable _ _)
      (ae_of_all _ fun t _ w _ => hd w t)
    exact h.2.differentiableAt
  convert hi.const_mul (α : ℂ) using 1 <;> rfl

/--
@isnad1 id=le.0h1v.s4.4bf94c3d1486 from=translated src=- shape=98bba06a vocab=c0d6529e
-/
theorem sinc_sixth_le_one (x : ℝ) : Real.sinc x ^ 6 ≤ 1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one x) 6
  simpa only [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, sq_abs, one_pow] using h

/--
@isnad1 id=le.0h1v.s6.4d21264af5f7 from=translated src=- shape=fbe36b82 vocab=6e3b1a7c
-/
theorem sinc_sixth_le_cauchy (x : ℝ) : Real.sinc x ^ 6 ≤ 2 / (1+x^2) := by
  have h1 := sinc_sixth_le_one x
  have hs : (Real.sinc x)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one x) 2
  have h4 : (Real.sinc x)^4 ≤ 1 := by nlinarith [sq_nonneg ((Real.sinc x)^2-1)]
  have hsin : x * Real.sinc x = Real.sin x := by
    by_cases hx : x=0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]; field_simp
  have hsin2 : (Real.sin x)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one x) 2
  have hprod : x^2 * Real.sinc x^6 ≤ 1 := by
    calc
      _ = (Real.sin x)^2 * (Real.sinc x)^4 := by rw [← hsin]; ring
      _ ≤ 1 * 1 := mul_le_mul hsin2 h4 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  apply (le_div_iff₀ (by positivity : 0 < 1+x^2)).mpr
  nlinarith

/--
@isnad1 id=le.2h3v.s5.10ce8d8b919d from=translated src=- shape=e9a55a0f vocab=7c56f008
-/
theorem plateauWindowReal_nonneg {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) (x : ℝ) :
    0 ≤ plateauWindowReal α τ x := by
  apply mul_nonneg hα
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => by positivity)

/--
@isnad1 id=eq.0h3v.s6.4fd629a989be from=translated src=- shape=f9d9e70b vocab=563fff7b
-/
theorem plateauWindowReal_change_variables (α τ x : ℝ) :
    plateauWindowReal α τ x =
      ∫ u : ℝ in α*(x-τ)..α*(x+τ), Real.sinc u ^ 6 := by
  unfold plateauWindowReal
  have h := intervalIntegral.smul_integral_comp_sub_mul
    (fun u : ℝ => Real.sinc u ^ 6) (a := -τ) (b := τ) α (α*x)
  simpa only [smul_eq_mul, ← mul_sub, sub_neg_eq_add] using h

/-- A deliberately nonoptimal absolute upper bound, independent of both scales.
@isnad1 id=le.2h3v.s5.fd07d640b44f from=translated src=- shape=ef2e9bc7 vocab=a2438edb
-/
theorem plateauWindowReal_le {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) (x : ℝ) :
    plateauWindowReal α τ x ≤ 2 * Real.pi := by
  rw [plateauWindowReal_change_variables]
  have hi : IntervalIntegrable (fun u : ℝ => Real.sinc u ^ 6) volume
      (α*(x-τ)) (α*(x+τ)) := (Real.continuous_sinc.pow 6).intervalIntegrable _ _
  have hc : Continuous (fun u : ℝ => 2/(1+u^2)) := by
    exact continuous_const.div (by fun_prop) (fun u => by positivity)
  have h := intervalIntegral.integral_mono (show α*(x-τ) ≤ α*(x+τ) by nlinarith)
    hi (hc.intervalIntegrable _ _) sinc_sixth_le_cauchy
  calc
    _ ≤ ∫ u : ℝ in α*(x-τ)..α*(x+τ), 2/(1+u^2) := h
    _ = 2 * (Real.arctan (α*(x+τ)) - Real.arctan (α*(x-τ))) := by
      simp_rw [show ∀ u : ℝ, 2/(1+u^2)=2*(1/(1+u^2)) by intro u; ring]
      rw [intervalIntegral.integral_const_mul, integral_one_div_one_add_sq]
    _ ≤ 2 * Real.pi := by
      linarith [Real.arctan_lt_pi_div_two (α*(x+τ)),
        Real.neg_pi_div_two_lt_arctan (α*(x-τ))]

/--
@isnad1 id=ex.0h0v.s6.3cac365e5525 from=translated src=- shape=3eb378c5 vocab=b464434b
-/
theorem exists_sinc_sixth_near_one : ∃ η > 0, ∀ x : ℝ, |x| ≤ η →
    1/2 ≤ Real.sinc x ^ 6 := by
  have hc := (Real.continuous_sinc.pow 6).continuousAt (x := 0)
  obtain ⟨η,hη,hcη⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  refine ⟨η/2,by positivity,?_⟩
  intro x hx
  have h := hcη (show dist x 0 < η by
    simpa [Real.dist_eq] using hx.trans_lt (half_lt_self hη))
  simp only [Pi.pow_apply, Real.sinc_zero, one_pow, Real.dist_eq] at h
  linarith [(abs_lt.mp h).1]

/--
@isnad1 id=le.5h4v.s7.cbc6d87c38ea from=translated src=- shape=cb02f9fd vocab=424b35aa
-/
theorem plateauWindowReal_lower {η α τ x : ℝ} (hη : 0 < η)
    (hs : ∀ u : ℝ, |u| ≤ η → 1/2 ≤ Real.sinc u ^ 6)
    (hα : 0 ≤ α) (hsize : η ≤ α*τ) (hx : |x| ≤ τ) :
    η/2 ≤ plateauWindowReal α τ x := by
  rw [plateauWindowReal_change_variables]
  have hx' := abs_le.mp hx
  have ha : α*(x-τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα (by linarith)
  have hb : 0 ≤ α*(x+τ) := mul_nonneg hα (by linarith)
  have hi : IntervalIntegrable (fun u : ℝ => Real.sinc u ^ 6) volume
      (α*(x-τ)) (α*(x+τ)) := (Real.continuous_sinc.pow 6).intervalIntegrable _ _
  by_cases hxx : 0 ≤ x
  · have hηb : η ≤ α*(x+τ) := by nlinarith
    have hsmall : η/2 ≤ ∫ u : ℝ in 0..η, Real.sinc u^6 := by
      have hm := intervalIntegral.integral_mono_on (μ := volume) hη.le
        (continuous_const.intervalIntegrable 0 η)
        ((Real.continuous_sinc.pow 6).intervalIntegrable 0 η)
        (fun u (hu : u ∈ Icc 0 η) => hs u (by simpa [abs_of_nonneg hu.1] using hu.2))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div, Pi.pow_apply] using hm
    exact hsmall.trans (intervalIntegral.integral_mono_interval ha hη.le hηb
      (ae_of_all _ fun _ => by positivity) hi)
  · have hηa : α*(x-τ) ≤ -η := by nlinarith
    have hsmall : η/2 ≤ ∫ u : ℝ in -η..0, Real.sinc u^6 := by
      have hm := intervalIntegral.integral_mono_on (μ := volume) (show -η ≤ 0 by linarith)
        (continuous_const.intervalIntegrable (-η) 0)
        ((Real.continuous_sinc.pow 6).intervalIntegrable (-η) 0)
        (fun u (hu : u ∈ Icc (-η) 0) => hs u (abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩))
      simpa only [intervalIntegral.integral_const, zero_sub, neg_neg, smul_eq_mul, mul_one_div, Pi.pow_apply] using hm
    exact hsmall.trans (intervalIntegral.integral_mono_interval hηa (by linarith) hb
      (ae_of_all _ fun _ => by positivity) hi)

/--
@isnad1 id=ex.0h0v.s6.b1c37a9e7d2d from=translated src=- shape=1b0a22fd vocab=f160e79a
-/
theorem plateauWindow_uniform_positive : ∃ η > 0, ∀ α τ x : ℝ,
    0 ≤ α → η ≤ α*τ → |x| ≤ τ → η/2 ≤ plateauWindowReal α τ x := by
  obtain ⟨η,hη,hs⟩ := exists_sinc_sixth_near_one
  exact ⟨η,hη,fun _ _ _ hα hsize hx => plateauWindowReal_lower hη hs hα hsize hx⟩

/--
@isnad1 id=le.1h2v.s7.81cb78a2ee92 from=translated src=- shape=54188977 vocab=9e5a6a50
-/
theorem scaled_sinc_sixth_decay {α : ℝ} (hα : 0 < α) (z : ℂ) :
    ‖entireSinc ((α : ℂ)*z)^6‖ ≤
      (2/min 1 α)^6 * Real.exp (6*α*|z.im|)/(1+‖z‖)^6 := by
  let c := min 1 α
  have hc : 0 < c := lt_min (by norm_num) hα
  have hd : c*(1+‖z‖) ≤ 1+α*‖z‖ := by
    have h1 : c ≤ 1 := min_le_left _ _
    have h2 : c ≤ α := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg z)]
  have hb := norm_entireSinc_decay ((α : ℂ)*z)
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    abs_mul, abs_of_pos hα, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hb
  have hb' : ‖entireSinc ((α : ℂ)*z)‖ ≤
      (2/c)*Real.exp (α*|z.im|)/(1+‖z‖) := by
    apply hb.trans
    calc
      _ ≤ 2*Real.exp (α*|z.im|)/(c*(1+‖z‖)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = _ := by field_simp
  have hh := pow_le_pow_left₀ (norm_nonneg _) hb' 6
  rw [← norm_pow, div_pow, mul_pow, ← Real.exp_nat_mul] at hh
  simpa [c, mul_assoc] using hh

/-- The compact convolution preserves sixth-order complex decay and adds type `6α`.
@isnad1 id=le.2h3v.s7.302a14dbe553 from=translated src=- shape=0bcc8294 vocab=691af1e5
-/
theorem plateauWindow_complex_decay {α τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (z : ℂ) :
    ‖plateauWindow α τ z‖ ≤
      (2*α*τ*((2/min 1 α)*(1+τ))^6) *
        Real.exp (6*α*|z.im|)/(1+‖z‖)^6 := by
  let C := ((2/min 1 α)*(1+τ))^6 * Real.exp (6*α*|z.im|)/(1+‖z‖)^6
  have hkernel (t : ℝ) (ht : t ∈ uIoc (-τ) τ) :
      ‖entireSinc ((α : ℂ)*(z-t))^6‖ ≤ C := by
    have ht' : |t| ≤ τ := by
      have hm : t ∈ Ioc (-τ) τ := by simpa [uIoc_of_le (show -τ ≤ τ by linarith)] using ht
      exact abs_le.mpr ⟨hm.1.le,hm.2⟩
    have hn : ‖z‖ ≤ ‖z-(t : ℂ)‖+τ := by
      calc
        _ ≤ ‖z-(t : ℂ)‖+‖(t : ℂ)‖ := norm_le_norm_sub_add z t
        _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using add_le_add_right ht' _
    have hp : 1+‖z‖ ≤ (1+τ)*(1+‖z-(t : ℂ)‖) := by
      nlinarith [norm_nonneg (z-(t : ℂ))]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖z‖) hp 6
    have hh := scaled_sinc_sixth_decay hα (z-t)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hh
    apply hh.trans
    dsimp [C]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      _ ≤ ((2/min 1 α)^6*Real.exp (6*α*|z.im|))*
          ((1+τ)*(1+‖z-(t : ℂ)‖))^6 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -τ) (b := τ) hkernel
  unfold plateauWindow
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  calc
    _ ≤ α*(C*|τ-(-τ)|) := mul_le_mul_of_nonneg_left hi hα.le
    _ = _ := by rw [abs_of_nonneg (by linarith : 0 ≤ τ-(-τ))]; dsimp [C]; ring

/--
@isnad1 id=ex.2h2v.s6.8d0ee8a327fc from=translated src=- shape=399ed8bd vocab=af936c2f
-/
theorem plateauWindow_exponential_type {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    ∃ C > 0, ∀ z : ℂ, ‖plateauWindow α τ z‖ ≤ C*Real.exp (6*α*|z.im|) := by
  refine ⟨2*α*τ*((2/min 1 α)*(1+τ))^6, by positivity, fun z => ?_⟩
  exact (plateauWindow_complex_decay hα hτ.le z).trans
    (div_le_self (by positivity) (one_le_pow₀ (by linarith [norm_nonneg z])))

/--
@isnad1 id=le.2h2v.s6.720250d9e913 from=translated src=- shape=2dd1c15e vocab=2aa3b29f
-/
theorem sinc_sixth_tail {α d : ℝ} (hα : 0 < α) (hd : d ≠ 0) :
    Real.sinc (α*d)^6 ≤ (1/(α*|d|))^6 := by
  have h : |Real.sinc (α*d)| ≤ 1/(α*|d|) := by
    rw [Real.sinc_of_ne_zero (mul_ne_zero hα.ne' hd), abs_div, abs_mul, abs_of_pos hα]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 6
  simpa only [show (6 : ℕ)=2*3 from rfl, pow_mul, sq_abs] using hh

/-- Outside the plateau, the distance from the whole integration interval controls the tail.
@isnad1 id=le.3h3v.s6.1da7cf468883 from=translated src=- shape=5f556d0d vocab=db05a73b
-/
theorem plateauWindowReal_tail {α τ x : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hx : τ < |x|) :
    plateauWindowReal α τ x ≤ 2*α*τ / (α*(|x|-τ))^6 := by
  have hi : IntervalIntegrable (fun t : ℝ => Real.sinc (α*(x-t))^6) volume (-τ) τ :=
    (Real.continuous_sinc.comp (by fun_prop) |>.pow 6).intervalIntegrable _ _
  have hpoint (t : ℝ) (ht : t ∈ Icc (-τ) τ) :
      Real.sinc (α*(x-t))^6 ≤ (1/(α*(|x|-τ)))^6 := by
    have ht' : |t| ≤ τ := abs_le.mpr ht
    have hd : |x|-τ ≤ |x-t| := by linarith [abs_sub_abs_le_abs_sub x t]
    have hdt : 0 < |x-t| := lt_of_lt_of_le (sub_pos.mpr hx) hd
    apply (sinc_sixth_tail hα (sub_ne_zero.mpr (fun h => by simp [h] at hdt))).trans
    exact pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (mul_pos hα (sub_pos.mpr hx))
        (mul_le_mul_of_nonneg_left hd hα.le)) 6
  have hm := intervalIntegral.integral_mono_on (μ := volume) (show -τ ≤ τ by linarith)
    hi (continuous_const.intervalIntegrable _ _) hpoint
  unfold plateauWindowReal
  calc
    _ ≤ α * ((τ-(-τ)) * (1/(α*(|x|-τ)))^6) := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using
        mul_le_mul_of_nonneg_left hm hα.le
    _ = _ := by rw [div_pow]; ring

/--
@isnad1 id=le.2h3v.s5.ff7afbe74577 from=translated src=- shape=defec27f vocab=a6a25222
-/
theorem norm_plateauWindow_real_le {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) (x : ℝ) :
    ‖plateauWindow α τ x‖ ≤ 2*Real.pi := by
  rw [plateauWindow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (plateauWindowReal_nonneg hα hτ x)]
  exact plateauWindowReal_le hα hτ x

/--
@isnad1 id=le.3h3v.s6.4b169eac082e from=translated src=- shape=9dee6784 vocab=ab424c88
-/
theorem norm_plateauWindow_real_tail {α τ x : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hx : τ < |x|) :
    ‖plateauWindow α τ x‖ ≤ 2*α*τ/(α*(|x|-τ))^6 := by
  rw [plateauWindow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (plateauWindowReal_nonneg hα.le hτ x)]
  exact plateauWindowReal_tail hα hτ hx

/--
@isnad1 id=le.4h6v.s8.50ae60ac5622 from=translated src=- shape=1c00ec17 vocab=691af1e5
-/
theorem mul_plateauWindow_decay {f : ℂ → ℂ} {α τ σ K : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (hf : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|)) (z : ℂ) :
    ‖f z * plateauWindow α τ z‖ ≤
      (K*(2*α*τ*((2/min 1 α)*(1+τ))^6)) *
        Real.exp ((σ+6*α)*|z.im|)/(1+‖z‖)^6 := by
  rw [norm_mul]
  apply (mul_le_mul (hf z) (plateauWindow_complex_decay hα hτ z)
    (norm_nonneg _) (by positivity)).trans_eq
  rw [add_mul, Real.exp_add]
  ring

end Erdos1133
