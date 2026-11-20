import Tengoku.Lmlf.LMLF.ODE.Wronskian
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equation-level tests for Abel's Wronskian identity

These examples instantiate the reusable theorem with the hypergeometric and
associated Legendre equations.
-/

open MeasureTheory Set
open scoped Interval

namespace LMLFTest.ODE

noncomputable section

private noncomputable def hypergeometricFirst (a b c : ℝ) (t : ℝ) : ℂ :=
  ((c - (a + b + 1) * t) / (t * (1 - t)) : ℝ)

private noncomputable def hypergeometricZero (a b : ℝ) (t : ℝ) : ℂ :=
  ((-(a * b) / (t * (1 - t))) : ℝ)

private theorem hypergeometricFirst_continuousOn (a b c : ℝ) :
    ContinuousOn (hypergeometricFirst a b c) (Ioo 0 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hden : t * (1 - t) ≠ 0 :=
    mul_ne_zero (ne_of_gt ht.1) (ne_of_gt (sub_pos.mpr ht.2))
  have hr : ContinuousAt (fun u : ℝ ↦ (c - (a + b + 1) * u) / (u * (1 - u))) t := by
    fun_prop
  change ContinuousAt
    (fun u : ℝ ↦ Complex.ofReal ((c - (a + b + 1) * u) / (u * (1 - u)))) t
  exact Complex.continuous_ofReal.continuousAt.comp' hr

private theorem hypergeometric_integral_factor (a b c x₀ x : ℝ)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Complex.exp (-∫ t in x₀..x, hypergeometricFirst a b c t) =
      (((x / x₀) ^ (-c : ℝ) * ((1 - x) / (1 - x₀)) ^ (c - a - b - 1) : ℝ) : ℂ) := by
  let d : ℝ := c - a - b - 1
  let f : ℝ → ℝ := fun t ↦ (c - (a + b + 1) * t) / (t * (1 - t))
  let F : ℝ → ℝ := fun t ↦ c * Real.log t - d * Real.log (1 - t)
  have hseg : uIcc x₀ x ⊆ Ioo (0 : ℝ) 1 := isPreconnected_Ioo.ordConnected.uIcc_subset hx₀ hx
  have hfderiv : ∀ t ∈ uIcc x₀ x, HasDerivAt F (f t) t := by
    intro t ht
    have htI := hseg ht
    have ht0 : t ≠ 0 := ne_of_gt htI.1
    have ht1 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr htI.2)
    have hlogt := (Real.hasDerivAt_log ht0).const_mul c
    have hlog1 := (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log ht1).const_mul d
    exact (hlogt.sub hlog1).congr_deriv (by dsimp [f, d]; field_simp; ring)
  have hfcont : ContinuousOn f (uIcc x₀ x) := by
    intro t ht
    have htI := hseg ht
    have hden : t * (1 - t) ≠ 0 :=
      mul_ne_zero (ne_of_gt htI.1) (ne_of_gt (sub_pos.mpr htI.2))
    apply ContinuousAt.continuousWithinAt
    dsimp only [f]
    fun_prop
  have hint : IntervalIntegrable f volume x₀ x := hfcont.intervalIntegrable
  have hint_eq : (∫ t in x₀..x, f t) = F x - F x₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hfderiv hint
  have hcx : hypergeometricFirst a b c = fun t ↦ (f t : ℂ) := by
    funext t
    rfl
  rw [hcx, intervalIntegral.integral_ofReal, hint_eq, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos (div_pos hx.1 hx₀.1),
    Real.rpow_def_of_pos (div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hx₀.2)), ← Real.exp_add]
  apply congrArg Real.exp
  dsimp [F, d]
  rw [Real.log_div (ne_of_gt hx.1) (ne_of_gt hx₀.1),
    Real.log_div (ne_of_gt (sub_pos.mpr hx.2)) (ne_of_gt (sub_pos.mpr hx₀.2))]
  ring

/-- C1: Abel's identity specialized to the hypergeometric equation on `(0,1)`.-/
theorem hypergeometric_wronskian (a b c : ℝ) (y₁ v₁ y₂ v₂ : ℝ → ℂ)
    (hy₁ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt y₁ (v₁ t) t)
    (hv₁ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt v₁ (-hypergeometricFirst a b c t * v₁ t - hypergeometricZero a b t * y₁ t) t)
    (hy₂ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt y₂ (v₂ t) t)
    (hv₂ : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt v₂ (-hypergeometricFirst a b c t * v₂ t - hypergeometricZero a b t * y₂ t) t)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    LMLF.ODE.wronskian y₁ v₁ y₂ v₂ x = LMLF.ODE.wronskian y₁ v₁ y₂ v₂ x₀ *
      (((x / x₀) ^ (-c : ℝ) * ((1 - x) / (1 - x₀)) ^ (c - a - b - 1) : ℝ) : ℂ) := by
  rw [LMLF.ODE.wronskian_eq_mul_cexp_integral isOpen_Ioo isPreconnected_Ioo
    (hypergeometricFirst_continuousOn a b c) hy₁ hv₁ hy₂ hv₂ hx₀ hx,
    hypergeometric_integral_factor a b c x₀ x hx₀ hx]

private noncomputable def legendreFirst (t : ℝ) : ℂ :=
  ((-2 * t / (1 - t ^ 2)) : ℝ)

private noncomputable def legendreZero (μ ν : ℂ) (t : ℝ) : ℂ :=
  ν * (ν + 1) / ((1 - t ^ 2 : ℝ) : ℂ) - μ ^ 2 / (((1 - t ^ 2 : ℝ) : ℂ) ^ 2)

private theorem legendreFirst_continuousOn : ContinuousOn legendreFirst (Ioo (-1 : ℝ) 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  have hr : ContinuousAt (fun u : ℝ ↦ -2 * u / (1 - u ^ 2)) t := by fun_prop
  change ContinuousAt (fun u : ℝ ↦ Complex.ofReal (-2 * u / (1 - u ^ 2))) t
  exact Complex.continuous_ofReal.continuousAt.comp' hr

private theorem legendre_integral_factor (x₀ x : ℝ)
    (hx₀ : x₀ ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Complex.exp (-∫ t in x₀..x, legendreFirst t) = (((1 - x₀ ^ 2) / (1 - x ^ 2) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun t ↦ -2 * t / (1 - t ^ 2)
  let F : ℝ → ℝ := fun t ↦ Real.log (1 - t ^ 2)
  have hseg : uIcc x₀ x ⊆ Ioo (-1 : ℝ) 1 := isPreconnected_Ioo.ordConnected.uIcc_subset hx₀ hx
  have hfderiv : ∀ t ∈ uIcc x₀ x, HasDerivAt F (f t) t := by
    intro t ht
    have htI := hseg ht
    have hpos : 0 < 1 - t ^ 2 := by nlinarith [htI.1, htI.2]
    have hinner : HasDerivAt (fun u : ℝ ↦ 1 - u ^ 2) (-2 * t) t := by
      exact ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2)).congr_deriv (by simp [id])
    exact (hinner.log (ne_of_gt hpos)).congr_deriv (by dsimp [f])
  have hfcont : ContinuousOn f (uIcc x₀ x) := by
    intro t ht
    have htI := hseg ht
    have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [htI.1, htI.2])
    apply ContinuousAt.continuousWithinAt
    dsimp only [f]
    fun_prop
  have hint : IntervalIntegrable f volume x₀ x := hfcont.intervalIntegrable
  have hint_eq : (∫ t in x₀..x, f t) = F x - F x₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hfderiv hint
  have hcx : legendreFirst = fun t ↦ (f t : ℂ) := by
    funext t
    rfl
  have hposx : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hposx₀ : 0 < 1 - x₀ ^ 2 := by nlinarith [hx₀.1, hx₀.2]
  rw [hcx, intervalIntegral.integral_ofReal, hint_eq, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 1
  dsimp [F]
  rw [neg_sub, Real.exp_sub, Real.exp_log hposx₀, Real.exp_log hposx]

/-- C2: Abel's identity specialized to the associated Legendre equation on `(-1,1)`.-/
theorem associatedLegendre_wronskian (μ ν : ℂ) (y₁ v₁ y₂ v₂ : ℝ → ℂ)
    (hy₁ : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt y₁ (v₁ t) t)
    (hv₁ : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt v₁ (-legendreFirst t * v₁ t - legendreZero μ ν t * y₁ t) t)
    (hy₂ : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt y₂ (v₂ t) t)
    (hv₂ : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt v₂ (-legendreFirst t * v₂ t - legendreZero μ ν t * y₂ t) t)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    LMLF.ODE.wronskian y₁ v₁ y₂ v₂ x = LMLF.ODE.wronskian y₁ v₁ y₂ v₂ x₀ *
      (((1 - x₀ ^ 2) / (1 - x ^ 2) : ℝ) : ℂ) := by
  rw [LMLF.ODE.wronskian_eq_mul_cexp_integral isOpen_Ioo isPreconnected_Ioo
    legendreFirst_continuousOn hy₁ hv₁ hy₂ hv₂ hx₀ hx,
    legendre_integral_factor x₀ x hx₀ hx]

end

end LMLFTest.ODE
