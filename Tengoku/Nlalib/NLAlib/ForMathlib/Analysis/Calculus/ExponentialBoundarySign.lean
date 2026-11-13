import Tengoku.Seed.Analysis.Calculus.ContDiff.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The real sign calculation for exponential boundary integrals

Integration by parts turns the negative boundary integral of `exp u * η'` into
the integral of `η * exp u * u'` when `η` vanishes at the endpoints. If `η` and
`u'` are nonnegative, the resulting integral is nonnegative. Derivatives are
only required in the interior, so individual pieces may meet at corners.

This is the real-variable calculation in Eremenko, *Herbert Stahl's proof of
the BMV conjecture* (2014), pp. 6–7, https://www.math.purdue.edu/~eremenko/dvi/bmv2.pdf.
It is a helper for atlas `trace-exponential-stahl`; constructing the spectral
surface and the boundary arcs with these properties is a separate task.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace NLAlib

/-- Integration by parts for an exponential weight, with explicit derivative
representatives and the endpoint terms retained. Only the open interval needs
two-sided derivatives; this permits applications to pieces with corners.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper).
@isnad1 id=eq.6h6v.s8.ed0da6fcc78b from=translated src=- shape=d23c6db3 vocab=aa193515
-/
theorem integral_exp_mul_deriv_eq_sub
    {u η u' η' : ℝ → ℝ} {a b : ℝ}
    (hu : ContinuousOn u [[a, b]]) (hη : ContinuousOn η [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hηη' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt η (η' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hη' : IntervalIntegrable η' volume a b) :
    (∫ x in a..b, Real.exp (u x) * η' x) =
      Real.exp (u b) * η b - Real.exp (u a) * η a -
        ∫ x in a..b, η x * Real.exp (u x) * u' x := by
  have hexp : ContinuousOn (fun x => Real.exp (u x)) [[a, b]] :=
    Real.continuous_exp.comp_continuousOn hu
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hexp hη (fun x hx => (huu' x hx).exp) hηη'
    (hu'.continuousOn_mul hexp) hη'
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hparts

/-- If the height function vanishes at both endpoints, the negative exponential
boundary integral equals an integral with no derivative on the height. This is
the integration-by-parts calculation in Eremenko (2014), pp. 6–7, used in the
positivity argument for atlas `trace-exponential-stahl`.
@isnad1 id=eq.8h6v.s8.94f471ee3e51 from=translated src=- shape=deac679f vocab=d5d10416
-/
theorem neg_integral_exp_mul_deriv_eq_of_endpoints_eq_zero
    {u η u' η' : ℝ → ℝ} {a b : ℝ}
    (hu : ContinuousOn u [[a, b]]) (hη : ContinuousOn η [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hηη' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt η (η' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hη' : IntervalIntegrable η' volume a b)
    (hηa : η a = 0) (hηb : η b = 0) :
    -(∫ x in a..b, Real.exp (u x) * η' x) =
      ∫ x in a..b, η x * Real.exp (u x) * u' x := by
  rw [integral_exp_mul_deriv_eq_sub hu hη huu' hηη' hu' hη', hηa, hηb]
  simp

/-- A nonnegative height and nondecreasing phase give a nonnegative negative
boundary integral when the height is zero at the endpoints. The hypotheses
record derivatives; positivity of the integral is proved, not assumed.
Source: Eremenko (2014), pp. 6–7; helper for atlas `trace-exponential-stahl`.
@isnad1 id=le.11h6v.s8.07710f186522 from=translated src=- shape=5e8bce54 vocab=bc2880a2
-/
theorem neg_integral_exp_mul_deriv_nonneg
    {u η u' η' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u [[a, b]]) (hη : ContinuousOn η [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hηη' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt η (η' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hη' : IntervalIntegrable η' volume a b)
    (hηa : η a = 0) (hηb : η b = 0)
    (hη_nonneg : ∀ x ∈ Icc a b, 0 ≤ η x)
    (hu'_nonneg : ∀ x ∈ Icc a b, 0 ≤ u' x) :
    0 ≤ -(∫ x in a..b, Real.exp (u x) * η' x) := by
  rw [neg_integral_exp_mul_deriv_eq_of_endpoints_eq_zero
    hu hη huu' hηη' hu' hη' hηa hηb]
  exact intervalIntegral.integral_nonneg hab fun x hx =>
    mul_nonneg (mul_nonneg (hη_nonneg x hx) (Real.exp_pos _).le) (hu'_nonneg x hx)

/-- The integration-by-parts identity persists for a finite chain of smooth
pieces. Interior endpoint terms cancel even when the height is nonzero at the
corners. The derivative representatives may differ on successive pieces, and
no derivative hypothesis is imposed at a corner. Source: the piecewise-smooth
boundary calculation in Eremenko (2014), pp. 6–7; helper for atlas
`trace-exponential-stahl`.
@isnad1 id=eq.8h6v.s9.f00cef5a4029 from=translated src=- shape=d2f0e28f vocab=f9439d6d
-/
theorem neg_sum_integral_exp_mul_deriv_eq_of_endpoints_eq_zero
    {u η : ℝ → ℝ} {u' η' : ℕ → ℝ → ℝ} {v : ℕ → ℝ} {n : ℕ}
    (hu : ∀ k < n, ContinuousOn u [[v k, v (k + 1)]])
    (hη : ∀ k < n, ContinuousOn η [[v k, v (k + 1)]])
    (huu' : ∀ k < n, ∀ x ∈ Ioo (min (v k) (v (k + 1))) (max (v k) (v (k + 1))),
      HasDerivAt u (u' k x) x)
    (hηη' : ∀ k < n, ∀ x ∈ Ioo (min (v k) (v (k + 1))) (max (v k) (v (k + 1))),
      HasDerivAt η (η' k x) x)
    (hu' : ∀ k < n, IntervalIntegrable (u' k) volume (v k) (v (k + 1)))
    (hη' : ∀ k < n, IntervalIntegrable (η' k) volume (v k) (v (k + 1)))
    (hηa : η (v 0) = 0) (hηb : η (v n) = 0) :
    -(∑ k ∈ Finset.range n, ∫ x in v k..v (k + 1), Real.exp (u x) * η' k x) =
      ∑ k ∈ Finset.range n, ∫ x in v k..v (k + 1), η x * Real.exp (u x) * u' k x := by
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl fun k hk =>
    integral_exp_mul_deriv_eq_sub (hu k (Finset.mem_range.mp hk))
      (hη k (Finset.mem_range.mp hk)) (huu' k (Finset.mem_range.mp hk))
      (hηη' k (Finset.mem_range.mp hk)) (hu' k (Finset.mem_range.mp hk))
      (hη' k (Finset.mem_range.mp hk))
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun j => Real.exp (u (v j)) * η (v j))] at hsum
  simp only [hηa, hηb, mul_zero, sub_self, zero_sub] at hsum
  exact neg_eq_iff_eq_neg.mpr hsum

/-- The negative boundary contribution of a finite chain is nonnegative when
the height and phase derivative are nonnegative on each piece and only the
two outer heights vanish. This allows corners with nonzero height.
Source: Eremenko (2014), pp. 6–7; helper for atlas `trace-exponential-stahl`.
atlas: trace-exponential-stahl (partial)
@isnad1 id=le.11h6v.s9.c4290030e308 from=translated src=- shape=0f91d752 vocab=508fa30c
-/
theorem neg_sum_integral_exp_mul_deriv_nonneg
    {u η : ℝ → ℝ} {u' η' : ℕ → ℝ → ℝ} {v : ℕ → ℝ} {n : ℕ}
    (hv : ∀ k < n, v k ≤ v (k + 1))
    (hu : ∀ k < n, ContinuousOn u [[v k, v (k + 1)]])
    (hη : ∀ k < n, ContinuousOn η [[v k, v (k + 1)]])
    (huu' : ∀ k < n, ∀ x ∈ Ioo (min (v k) (v (k + 1))) (max (v k) (v (k + 1))),
      HasDerivAt u (u' k x) x)
    (hηη' : ∀ k < n, ∀ x ∈ Ioo (min (v k) (v (k + 1))) (max (v k) (v (k + 1))),
      HasDerivAt η (η' k x) x)
    (hu' : ∀ k < n, IntervalIntegrable (u' k) volume (v k) (v (k + 1)))
    (hη' : ∀ k < n, IntervalIntegrable (η' k) volume (v k) (v (k + 1)))
    (hηa : η (v 0) = 0) (hηb : η (v n) = 0)
    (hη_nonneg : ∀ k < n, ∀ x ∈ Icc (v k) (v (k + 1)), 0 ≤ η x)
    (hu'_nonneg : ∀ k < n, ∀ x ∈ Icc (v k) (v (k + 1)), 0 ≤ u' k x) :
    0 ≤ -(∑ k ∈ Finset.range n, ∫ x in v k..v (k + 1), Real.exp (u x) * η' k x) := by
  rw [neg_sum_integral_exp_mul_deriv_eq_of_endpoints_eq_zero
    hu hη huu' hηη' hu' hη' hηa hηb]
  apply Finset.sum_nonneg
  intro k hk
  have hkn := Finset.mem_range.mp hk
  exact intervalIntegral.integral_nonneg (hv k hkn) fun x hx =>
    mul_nonneg (mul_nonneg (hη_nonneg k hkn x hx) (Real.exp_pos _).le)
      (hu'_nonneg k hkn x hx)

/-- The normalized real boundary contribution in the Stahl–Eremenko sign
calculation equals a manifestly nonnegative integral for `C¹` functions.
Source: Eremenko (2014), pp. 6–7; helper for atlas `trace-exponential-stahl`.
@isnad1 id=and.7h4v.s8.fcaba8eff432 from=translated src=- shape=ef51b288 vocab=7cb03529
-/
theorem neg_inv_pi_mul_integral_exp_mul_deriv_eq_and_nonneg
    {u η : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    (hηa : η a = 0) (hηb : η b = 0)
    (hη_nonneg : ∀ x ∈ Icc a b, 0 ≤ η x)
    (hu'_nonneg : ∀ x ∈ Icc a b, 0 ≤ deriv u x) :
    (-(Real.pi⁻¹) * ∫ x in a..b, Real.exp (u x) * deriv η x) =
        Real.pi⁻¹ * ∫ x in a..b, η x * Real.exp (u x) * deriv u x ∧
      0 ≤ -(Real.pi⁻¹) * ∫ x in a..b, Real.exp (u x) * deriv η x := by
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdη : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hi := neg_integral_exp_mul_deriv_eq_of_endpoints_eq_zero
    hu.continuous.continuousOn hη.continuous.continuousOn
    (fun x _ => (hdu x).hasDerivAt) (fun x _ => (hdη x).hasDerivAt)
    (hu.continuous_deriv_one.intervalIntegrable a b)
    (hη.continuous_deriv_one.intervalIntegrable a b) hηa hηb
  have hpos : 0 ≤ ∫ x in a..b, η x * Real.exp (u x) * deriv u x :=
    intervalIntegral.integral_nonneg hab fun x hx =>
      mul_nonneg (mul_nonneg (hη_nonneg x hx) (Real.exp_pos _).le) (hu'_nonneg x hx)
  constructor
  · calc
      _ = Real.pi⁻¹ * -(∫ x in a..b, Real.exp (u x) * deriv η x) := by ring
      _ = _ := by rw [hi]
  · calc
      _ = Real.pi⁻¹ * -(∫ x in a..b, Real.exp (u x) * deriv η x) := by ring
      _ = _ := by rw [hi]
      _ ≥ 0 := mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hpos

end NLAlib
