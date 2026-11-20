import Tengoku.Seed.Analysis.Calculus.MeanValue
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.Topology.Order.IntermediateValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# First-order homogeneous scalar equations

The exponential-of-an-oriented-integral solution formula for homogeneous
first-order scalar equations on an open real interval, for real and complex
values. The complex statements still have a real independent variable.
-/

open MeasureTheory Set
open scoped Interval

namespace LMLF.ODE

private theorem integral_hasDerivAt_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {a : ℝ → E} (ha : ContinuousOn a I) {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    HasDerivAt (fun u ↦ ∫ t in x₀..u, a t) (a x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (ha.mono (hIc.ordConnected.uIcc_subset hx₀ hx)).intervalIntegrable
  · exact ha.stronglyMeasurableAtFilter hI x hx
  · exact ha.continuousAt (hI.mem_nhds hx)

/-- Every real constant times the exponential of the negative integral solves
the corresponding first-order homogeneous equation.
@isnad1 id=hasderiv.5h5v.s7.001d0fb7d672 from=translated src=- shape=9dc648b4 vocab=1c955384
-/
theorem hasDerivAt_const_mul_exp_neg_integral
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {a : ℝ → ℝ} (ha : ContinuousOn a I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (c : ℝ) :
    ∀ x ∈ I,
      HasDerivAt
        (fun u ↦ c * Real.exp (-∫ t in x₀..u, a t))
        (-a x * (c * Real.exp (-∫ t in x₀..x, a t))) x := by
  intro x hx
  have hA := integral_hasDerivAt_of_continuousOn hI hIc ha hx₀ hx
  exact (hA.neg.exp.const_mul c).congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- Every real solution of `w' = -a w` agrees on the interval with its
basepoint-normalized exponential-of-an-integral formula.
@isnad1 id=eqon.5h4v.s7.a223b9a5072a from=translated src=- shape=a8b2e86f vocab=ee90aaac
-/
theorem eqOn_const_mul_exp_neg_integral_of_hasDerivAt
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {a w : ℝ → ℝ} (ha : ContinuousOn a I)
    (hw : ∀ x ∈ I, HasDerivAt w (-a x * w x) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    Set.EqOn w
      (fun x ↦ w x₀ * Real.exp (-∫ t in x₀..x, a t)) I := by
  let A : ℝ → ℝ := fun u ↦ ∫ t in x₀..u, a t
  let E : ℝ → ℝ := fun u ↦ Real.exp (A u) * w u
  have hE : ∀ x ∈ I, HasDerivAt E 0 x := by
    intro x hx
    have hA : HasDerivAt A (a x) x :=
      integral_hasDerivAt_of_continuousOn hI hIc ha hx₀ hx
    have h := hA.exp.mul (hw x hx)
    exact h.congr_deriv (by ring)
  intro x hx
  have hconst : E x = E x₀ :=
    hI.is_const_of_deriv_eq_zero hIc
      (fun z hz ↦ (hE z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hE z hz).deriv) hx hx₀
  have hproduct : Real.exp (A x) * w x = w x₀ := by
    simpa [E, A] using hconst
  calc
    w x = (Real.exp (A x))⁻¹ * (Real.exp (A x) * w x) := by
      simp [Real.exp_ne_zero]
    _ = (Real.exp (A x))⁻¹ * w x₀ := by rw [hproduct]
    _ = w x₀ * Real.exp (-A x) := by
      rw [Real.exp_neg]
      ac_rfl
    _ = w x₀ * Real.exp (-∫ t in x₀..x, a t) := by rfl

/-- Every complex constant times the complex exponential of the negative
integral solves the corresponding real-time first-order homogeneous equation.
@isnad1 id=hasderiv.5h5v.s7.bacdabfc4dac from=translated src=- shape=f9680fb5 vocab=55047841
-/
theorem hasDerivAt_const_mul_cexp_neg_integral
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {a : ℝ → ℂ} (ha : ContinuousOn a I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (c : ℂ) :
    ∀ x ∈ I,
      HasDerivAt
        (fun u ↦ c * Complex.exp (-∫ t in x₀..u, a t))
        (-a x * (c * Complex.exp (-∫ t in x₀..x, a t))) x := by
  intro x hx
  have hA := integral_hasDerivAt_of_continuousOn hI hIc ha hx₀ hx
  exact (hA.neg.cexp.const_mul c).congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- Every complex-valued real-time solution of `w' = -a w` agrees on the
interval with its basepoint-normalized exponential-of-an-integral formula.
@isnad1 id=eqon.5h4v.s7.b12d0a00f063 from=translated src=- shape=73370017 vocab=63f4cfc5
-/
theorem eqOn_const_mul_cexp_neg_integral_of_hasDerivAt
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {a w : ℝ → ℂ} (ha : ContinuousOn a I)
    (hw : ∀ x ∈ I, HasDerivAt w (-a x * w x) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    Set.EqOn w
      (fun x ↦ w x₀ * Complex.exp (-∫ t in x₀..x, a t)) I := by
  let A : ℝ → ℂ := fun u ↦ ∫ t in x₀..u, a t
  let E : ℝ → ℂ := fun u ↦ Complex.exp (A u) * w u
  have hE : ∀ x ∈ I, HasDerivAt E 0 x := by
    intro x hx
    have hA : HasDerivAt A (a x) x :=
      integral_hasDerivAt_of_continuousOn hI hIc ha hx₀ hx
    have h := hA.cexp.mul (hw x hx)
    exact h.congr_deriv (by ring)
  intro x hx
  have hconst : E x = E x₀ :=
    hI.is_const_of_deriv_eq_zero hIc
      (fun z hz ↦ (hE z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hE z hz).deriv) hx hx₀
  have hproduct : Complex.exp (A x) * w x = w x₀ := by
    simpa [E, A] using hconst
  calc
    w x = (Complex.exp (A x))⁻¹ * (Complex.exp (A x) * w x) := by
      simp [Complex.exp_ne_zero]
    _ = (Complex.exp (A x))⁻¹ * w x₀ := by rw [hproduct]
    _ = w x₀ * Complex.exp (-A x) := by
      rw [Complex.exp_neg]
      ac_rfl
    _ = w x₀ * Complex.exp (-∫ t in x₀..x, a t) := by rfl

end LMLF.ODE
