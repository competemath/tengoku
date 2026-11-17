import Tengoku.FltAnthropic.Theorems.Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter

namespace P2mKcBalancedBeta

abbrev μ0 : Measure ℝ := volume.restrict (Ioi (0:ℝ))

/--
@isnad1 id=eventual.0h0v.s4.466dab02c8a6 from=translated src=- shape=7a53fbac vocab=ee1c071d
-/
theorem ae_pos_μ0 : ∀ᵐ x ∂μ0, 0 < x := ae_restrict_mem measurableSet_Ioi

/--
@isnad1 id=eq.1h2v.s5.094412e2774a from=translated src=- shape=a392af6f vocab=a04265b8
-/
theorem inv_ofReal_cpow {x : ℝ} (hx : 0 < x) (r : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ r = (x : ℂ) ^ (-r) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact pi_ne_zero.symm), cpow_neg]

/--
@isnad1 id=eq.2h3v.s6.53654ec592ae from=translated src=- shape=0f5f63b2 vocab=b84fa9bd
-/
theorem div_ofReal_cpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (r : ℂ) :
    ((x / y : ℝ) : ℂ) ^ r = (x : ℂ) ^ r * (y : ℂ) ^ (-r) := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hx (inv_pos.mpr hy).le, inv_ofReal_cpow hy]

/--
@isnad1 id=eq.2h3v.s6.5c4ffe78dfe3 from=translated src=- shape=8f24f55f vocab=3b8dd6ab
-/
theorem mul_ofReal_cpow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℂ) :
    ((x * y : ℝ) : ℂ) ^ r = (x : ℂ) ^ r * (y : ℂ) ^ r := by
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hx hy]

/--
@isnad1 id=eq.1h2v.s5.2679cbb4fb02 from=translated src=- shape=955acc88 vocab=80da2760
-/
theorem norm_ofReal_cpow {x : ℝ} (hx : 0 < x) (r : ℂ) : ‖(x : ℂ) ^ r‖ = x ^ r.re :=
  norm_cpow_eq_rpow_re_of_pos hx r

/--
@isnad1 id=eq.1h2v.s5.2c6cd123d68e from=translated src=- shape=49c25c64 vocab=e3513ad6
-/
theorem ofReal_mul_cpow {x : ℝ} (hx : 0 < x) (r : ℂ) : (x : ℂ) * (x : ℂ) ^ r = (x : ℂ) ^ (r + 1) := by
  rw [cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_one, mul_comm]

/--
@isnad1 id=eq.1h3v.s6.8f39ac782fc0 from=translated src=- shape=be8ade65 vocab=e3513ad6
-/
theorem cpow_add_ofReal {x : ℝ} (hx : 0 < x) (r s : ℂ) :
    (x : ℂ) ^ r * (x : ℂ) ^ s = (x : ℂ) ^ (r + s) :=
  (cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')).symm

/--
@isnad1 id=and.2h2v.s8.17f59c3bbcc7 from=translated src=- shape=1865e57f vocab=c8f90654
-/
theorem beta (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) :=
  Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div a b ha hb

/--
@isnad1 id=integrab.2h2v.s7.6bdf417e0535 from=translated src=- shape=469eee05 vocab=42feb728
-/
theorem integrableOn_beta {a c : ℂ} (ha : 0 < a.re) (hc : 0 < (c - a).re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-c)) (Ioi 0) := by
  have h := (beta a (c - a) ha hc).1
  refine h.congr_fun (fun v hv => ?_) measurableSet_Ioi
  congr 2; ring

/--
@isnad1 id=integrab.2h2v.s6.55d9dde163b0 from=translated src=- shape=498748ff vocab=fb9af8a3
-/
theorem integrableOn_betaR {a c : ℝ} (ha : 0 < a) (hc : a < c) :
    IntegrableOn (fun v : ℝ => v ^ (a - 1) * (1 + v) ^ (-c)) (Ioi 0) := by
  have h := (integrableOn_beta (a := (a : ℂ)) (c := (c : ℂ)) (by simpa) (by simp; linarith)).norm
  refine IntegrableOn.congr_fun h (fun v hv => ?_) measurableSet_Ioi
  have hv' : (0:ℝ) < v := hv
  rw [norm_mul, norm_ofReal_cpow hv', norm_ofReal_cpow (by linarith)]
  simp

def F0 (A a b D : ℂ) (x y : ℝ) : ℂ :=
  (x : ℂ) ^ (A - 1) * (((1 + x : ℝ)) : ℂ) ^ (-a) *
    ((y : ℂ) ^ (a + D - 1) * (((1 + y : ℝ)) : ℂ) ^ (-b)) * (((1 + x + y : ℝ)) : ℂ) ^ (-D)

def h (A a b D : ℂ) (x z : ℝ) : ℂ :=
  (x : ℂ) ^ (A - 1) * ((z : ℂ) ^ (a + D - 1) * (((1 + z : ℝ)) : ℂ) ^ (-D)) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b)

/--
@isnad1 id=eq.1h5v.s6.b1e8c2580672 from=translated src=- shape=2580148d vocab=21de1d7f
-/
theorem step1 (A a b D : ℂ) {x : ℝ} (hx : 0 < x) :
    ∫ y in Ioi (0:ℝ), F0 A a b D x y = ∫ z in Ioi (0:ℝ), h A a b D x z := by
  have hx1 : 0 < 1 + x := by linarith
  have hs := integral_comp_mul_left_Ioi (fun y : ℝ => F0 A a b D x y) 0 hx1
  rw [mul_zero] at hs
  have e : ∫ y in Ioi (0:ℝ), F0 A a b D x y = ∫ z in Ioi (0:ℝ), (1 + x) • F0 A a b D x ((1 + x) * z) := by
    rw [integral_smul, hs, smul_smul, mul_inv_cancel₀ hx1.ne', one_smul]
  rw [e]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  have hz' : (0:ℝ) < z := hz
  simp only [F0, h, Complex.real_smul]
  rw [mul_ofReal_cpow hx1.le hz'.le, show (1 + x + (1 + x) * z : ℝ) = (1 + x) * (1 + z) by ring,
    mul_ofReal_cpow hx1.le (by linarith), show (1 + (1 + x) * z : ℝ) = 1 + z + x * z by ring]
  have hX : ((1 + x : ℝ) : ℂ) * (((1 + x : ℝ)) : ℂ) ^ (-a) *
      ((((1 + x : ℝ)) : ℂ) ^ (a + D - 1) * (((1 + x : ℝ)) : ℂ) ^ (-D)) = 1 := by
    rw [ofReal_mul_cpow hx1, cpow_add_ofReal hx1, cpow_add_ofReal hx1,
      show -a + 1 + (a + D - 1 + -D) = 0 by ring, cpow_zero]
  calc ((1 + x : ℝ) : ℂ) * ((x : ℂ) ^ (A - 1) * (((1 + x : ℝ)) : ℂ) ^ (-a) *
        ((((1 + x : ℝ)) : ℂ) ^ (a + D - 1) * (z : ℂ) ^ (a + D - 1) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b)) *
        ((((1 + x : ℝ)) : ℂ) ^ (-D) * (((1 + z : ℝ)) : ℂ) ^ (-D)))
      = (((1 + x : ℝ) : ℂ) * (((1 + x : ℝ)) : ℂ) ^ (-a) *
          ((((1 + x : ℝ)) : ℂ) ^ (a + D - 1) * (((1 + x : ℝ)) : ℂ) ^ (-D))) *
        ((x : ℂ) ^ (A - 1) * ((z : ℂ) ^ (a + D - 1) * (((1 + z : ℝ)) : ℂ) ^ (-D)) *
          (((1 + z + x * z : ℝ)) : ℂ) ^ (-b)) := by ring
    _ = _ := by rw [hX, one_mul]

/--
@isnad1 id=eq.3h5v.s7.77b098f52670 from=translated src=- shape=768ed941 vocab=ff920844
-/
theorem step3 (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) {z : ℝ} (hz : 0 < z) :
    ∫ x in Ioi (0:ℝ), h A a b D x z
      = Complex.Gamma A * Complex.Gamma (b - A) / Complex.Gamma b *
        ((z : ℂ) ^ (a + D - A - 1) * (((1 + z : ℝ)) : ℂ) ^ (-((a + D - A) + (b - a)))) := by
  have hz1 : 0 < 1 + z := by linarith
  set bb : ℝ := (1 + z) / z with hbb
  have hbb0 : 0 < bb := by rw [hbb]; positivity

  have e0 : ∫ x in Ioi (0:ℝ), h A a b D x z = ((z : ℂ) ^ (a + D - 1) * (((1 + z : ℝ)) : ℂ) ^ (-D)) *
      ∫ x in Ioi (0:ℝ), (x : ℂ) ^ (A - 1) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b) := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [h]; ring

  have hs := integral_comp_mul_left_Ioi (fun x : ℝ => (x : ℂ) ^ (A - 1) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b))
    0 hbb0
  rw [mul_zero] at hs
  have e1 : ∫ x in Ioi (0:ℝ), (x : ℂ) ^ (A - 1) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b)
      = ∫ ξ in Ioi (0:ℝ), bb • ((((bb * ξ : ℝ)) : ℂ) ^ (A - 1) * (((1 + z + bb * ξ * z : ℝ)) : ℂ) ^ (-b)) := by
    rw [integral_smul, hs, smul_smul, mul_inv_cancel₀ hbb0.ne', one_smul]
  have e2 : ∫ ξ in Ioi (0:ℝ), bb • ((((bb * ξ : ℝ)) : ℂ) ^ (A - 1) * (((1 + z + bb * ξ * z : ℝ)) : ℂ) ^ (-b))
      = ((bb : ℂ) ^ A * (((1 + z : ℝ)) : ℂ) ^ (-b)) *
        ∫ ξ in Ioi (0:ℝ), (ξ : ℂ) ^ (A - 1) * (((1 + ξ : ℝ)) : ℂ) ^ (-(A + (b - A))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    have hξ' : (0:ℝ) < ξ := hξ
    simp only [Complex.real_smul]
    rw [mul_ofReal_cpow hbb0.le hξ'.le, show (1 + z + bb * ξ * z : ℝ) = (1 + z) * (1 + ξ) by
        rw [hbb]; field_simp, mul_ofReal_cpow hz1.le (by linarith), show -(A + (b - A)) = -b by ring]
    have : (bb : ℂ) * (bb : ℂ) ^ (A - 1) = (bb : ℂ) ^ A := by rw [ofReal_mul_cpow hbb0]; congr 1; ring
    rw [← this]; ring
  rw [e0, e1, e2, (beta A (b - A) hA hbA).2, show A + (b - A) = b by ring, hbb, div_ofReal_cpow hz1.le hz]
  have k1 : (z : ℂ) ^ (a + D - 1) * (z : ℂ) ^ (-A) = (z : ℂ) ^ (a + D - A - 1) := by
    rw [cpow_add_ofReal hz]; congr 1; ring
  have k2 : (((1 + z : ℝ)) : ℂ) ^ (-D) * (((1 + z : ℝ)) : ℂ) ^ A * (((1 + z : ℝ)) : ℂ) ^ (-b)
      = (((1 + z : ℝ)) : ℂ) ^ (-((a + D - A) + (b - a))) := by
    rw [cpow_add_ofReal hz1, cpow_add_ofReal hz1]; congr 1; ring
  calc (z : ℂ) ^ (a + D - 1) * (((1 + z : ℝ)) : ℂ) ^ (-D) *
        ((((1 + z : ℝ)) : ℂ) ^ A * (z : ℂ) ^ (-A) * (((1 + z : ℝ)) : ℂ) ^ (-b) *
          (Complex.Gamma A * Complex.Gamma (b - A) / Complex.Gamma b))
      = Complex.Gamma A * Complex.Gamma (b - A) / Complex.Gamma b *
        (((z : ℂ) ^ (a + D - 1) * (z : ℂ) ^ (-A)) *
          ((((1 + z : ℝ)) : ℂ) ^ (-D) * (((1 + z : ℝ)) : ℂ) ^ A * (((1 + z : ℝ)) : ℂ) ^ (-b))) := by ring
    _ = _ := by rw [k1, k2]

def IB (A b : ℝ) : ℝ := ∫ ξ in Ioi (0:ℝ), ξ ^ (A - 1) * (1 + ξ) ^ (-b)

/--
@isnad1 id=eq.2h6v.s7.bdfeff8fa9bc from=translated src=- shape=f5b07c8c vocab=d2983dd8
-/
theorem norm_h (A a b D : ℂ) {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    ‖h A a b D x z‖ = x ^ (A.re - 1) * (z ^ ((a + D).re - 1) * (1 + z) ^ (-D.re)) * (1 + z + x * z) ^ (-b.re) := by
  simp only [h, norm_mul, norm_ofReal_cpow hx, norm_ofReal_cpow hz, sub_re, one_re]
  rw [norm_ofReal_cpow (by linarith), norm_ofReal_cpow (by positivity), neg_re, neg_re]

/--
@isnad1 id=eq.1h5v.s7.eef84b05ea67 from=translated src=- shape=620a1520 vocab=8e86d3ed
-/
theorem step3R (A a b D : ℂ) {z : ℝ} (hz : 0 < z) :
    ∫ x, ‖h A a b D x z‖ ∂μ0
      = IB A.re b.re * (z ^ ((a + D).re - A.re - 1) * (1 + z) ^ (-(D.re - A.re + b.re))) := by
  have hz1 : 0 < 1 + z := by linarith
  set bb : ℝ := (1 + z) / z with hbb
  have hbb0 : 0 < bb := by rw [hbb]; positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_h A a b D hx hz)]
  have e0 : ∫ x in Ioi (0:ℝ), x ^ (A.re - 1) * (z ^ ((a + D).re - 1) * (1 + z) ^ (-D.re)) * (1 + z + x * z) ^ (-b.re)
      = (z ^ ((a + D).re - 1) * (1 + z) ^ (-D.re)) *
        ∫ x in Ioi (0:ℝ), x ^ (A.re - 1) * (1 + z + x * z) ^ (-b.re) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hs := integral_comp_mul_left_Ioi (fun x : ℝ => x ^ (A.re - 1) * (1 + z + x * z) ^ (-b.re)) 0 hbb0
  rw [mul_zero] at hs
  have e1 : ∫ x in Ioi (0:ℝ), x ^ (A.re - 1) * (1 + z + x * z) ^ (-b.re)
      = ∫ ξ in Ioi (0:ℝ), bb • ((bb * ξ) ^ (A.re - 1) * (1 + z + bb * ξ * z) ^ (-b.re)) := by
    rw [integral_smul, hs, smul_smul, mul_inv_cancel₀ hbb0.ne', one_smul]
  have e2 : ∫ ξ in Ioi (0:ℝ), bb • ((bb * ξ) ^ (A.re - 1) * (1 + z + bb * ξ * z) ^ (-b.re))
      = (bb ^ A.re * (1 + z) ^ (-b.re)) * IB A.re b.re := by
    rw [IB, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    have hξ' : (0:ℝ) < ξ := hξ
    simp only [smul_eq_mul]
    rw [Real.mul_rpow hbb0.le hξ'.le, show (1 + z + bb * ξ * z : ℝ) = (1 + z) * (1 + ξ) by
        rw [hbb]; field_simp, Real.mul_rpow hz1.le (by linarith)]
    have : bb * bb ^ (A.re - 1) = bb ^ A.re := by
      rw [show bb * bb ^ (A.re - 1) = bb ^ (1:ℝ) * bb ^ (A.re - 1) by rw [Real.rpow_one], ← Real.rpow_add hbb0]
      congr 1; ring
    rw [← this]; ring
  rw [e0, e1, e2, hbb, Real.div_rpow hz1.le hz.le]
  have k1 : z ^ ((a + D).re - 1) / z ^ A.re = z ^ ((a + D).re - A.re - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hz.le, ← Real.rpow_add hz]; congr 1; ring
  have k2 : (1 + z) ^ (-D.re) * (1 + z) ^ A.re * (1 + z) ^ (-b.re) = (1 + z) ^ (-(D.re - A.re + b.re)) := by
    rw [← Real.rpow_add hz1, ← Real.rpow_add hz1]; congr 1; ring
  calc z ^ ((a + D).re - 1) * (1 + z) ^ (-D.re) * ((1 + z) ^ A.re / z ^ A.re * (1 + z) ^ (-b.re) * IB A.re b.re)
      = IB A.re b.re * ((z ^ ((a + D).re - 1) / z ^ A.re) *
          ((1 + z) ^ (-D.re) * (1 + z) ^ A.re * (1 + z) ^ (-b.re))) := by ring
    _ = _ := by rw [k1, k2]

/--
@isnad1 id=measurab.0h4v.s4.2d2554f19eab from=translated src=- shape=b7af6b88 vocab=af1bbf6f
-/
theorem measurable_h (A a b D : ℂ) : Measurable (Function.uncurry (h A a b D)) := by
  unfold h
  refine Measurable.mul (Measurable.mul ?_ (Measurable.mul ?_ ?_)) ?_
  · exact (Complex.measurable_ofReal.comp measurable_fst).pow_const _
  · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  · exact (Complex.measurable_ofReal.comp (by fun_prop)).pow_const _
  · exact (Complex.measurable_ofReal.comp (by fun_prop)).pow_const _

/--
@isnad1 id=integrab.3h5v.s6.de8e90d44f3d from=translated src=- shape=8baf5819 vocab=a2fcf96f
-/
theorem integrable_h_section (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) {z : ℝ} (hz : 0 < z) :
    Integrable (fun x : ℝ => h A a b D x z) μ0 := by
  have hz1 : 0 < 1 + z := by linarith
  set bb : ℝ := (1 + z) / z with hbb
  have hbb0 : 0 < bb := by rw [hbb]; positivity
  have hf : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (A - 1) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b)) (Ioi 0) := by
    have key : IntegrableOn (fun ξ : ℝ => (((bb * ξ : ℝ)) : ℂ) ^ (A - 1) * (((1 + z + bb * ξ * z : ℝ)) : ℂ) ^ (-b))
        (Ioi 0) := by
      have hB := (integrableOn_beta hA hbA).const_mul ((bb : ℂ) ^ (A - 1) * (((1 + z : ℝ)) : ℂ) ^ (-b))
      refine IntegrableOn.congr_fun hB (fun ξ hξ => ?_) measurableSet_Ioi
      have hξ' : (0:ℝ) < ξ := hξ
      rw [mul_ofReal_cpow hbb0.le hξ'.le, show (1 + z + bb * ξ * z : ℝ) = (1 + z) * (1 + ξ) by
        rw [hbb]; field_simp, mul_ofReal_cpow hz1.le (by linarith)]
      ring
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => (x : ℂ) ^ (A - 1) * (((1 + z + x * z : ℝ)) : ℂ) ^ (-b)) 0 hbb0).mp key
    rwa [mul_zero] at this
  have h2 := hf.const_mul ((z : ℂ) ^ (a + D - 1) * (((1 + z : ℝ)) : ℂ) ^ (-D))
  refine (IntegrableOn.congr_fun h2 (fun x hx => ?_) measurableSet_Ioi)
  simp only [h]; ring

/--
@isnad1 id=integrab.4h4v.s7.11d977b0ee90 from=translated src=- shape=28165285 vocab=0107f45e
-/
theorem integrable_h (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) (haD : 0 < (a + D - A).re)
    (hba : 0 < (b - a).re) :
    Integrable (Function.uncurry (h A a b D)) (μ0.prod μ0) := by
  rw [integrable_prod_iff' (measurable_h A a b D).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_pos_μ0] with z hz
    exact integrable_h_section A a b D hA hbA hz
  · have heq : (fun z => ∫ x, ‖Function.uncurry (h A a b D) (x, z)‖ ∂μ0) =ᵐ[μ0]
        fun z => IB A.re b.re * (z ^ ((a + D).re - A.re - 1) * (1 + z) ^ (-(D.re - A.re + b.re))) := by
      filter_upwards [ae_pos_μ0] with z hz
      exact step3R A a b D hz
    refine Integrable.congr ?_ heq.symm
    refine Integrable.const_mul ?_ _
    have hI := integrableOn_betaR (a := (a + D).re - A.re) (c := D.re - A.re + b.re)
      (by simpa using haD) (by have := hba; simp only [sub_re, add_re] at this ⊢; linarith)
    exact hI

/--
@isnad1 id=eq.4h4v.s8.2a900ae8131e from=translated src=- shape=b1e980b4 vocab=7d781980
-/
theorem main (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) (haD : 0 < (a + D - A).re)
    (hba : 0 < (b - a).re) :
    ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), F0 A a b D x y
      = Complex.Gamma A * Complex.Gamma (b - A) * Complex.Gamma (a + D - A) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => step1 A a b D hx),
    integral_integral_swap (integrable_h A a b D hA hbA haD hba),
    setIntegral_congr_fun measurableSet_Ioi (fun z hz => step3 A a b D hA hbA hz), integral_const_mul,
    (beta (a + D - A) (b - a) haD hba).2, show a + D - A + (b - a) = D + b - A by ring, div_mul_div_comm]
  ring

end P2mKcBalancedBeta

end

/--
@isnad1 id=eq.4h4v.s8.e19138fcbecb from=translated src=- shape=da92945f vocab=6c137a83
-/
theorem solution
    (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) (haD : 0 < (a + D - A).re) (hba : 0 < (b - a).re) :
    ∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)
      = Complex.Gamma A * Complex.Gamma (b - A) * Complex.Gamma (a + D - A) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A)) :=
  P2mKcBalancedBeta.main A a b D hA hbA haD hba
