import Tengoku.PshdLean.PshLines.Regularization.RadialPoissonSlope
import Tengoku.PshdLean.PshLines.Regularization.RadialCumulativeSign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The radial Poisson primitive

The radial Poisson slope can be integrated from a positive reference radius.
On the positive half-line, the resulting primitive has the prescribed first
derivative and satisfies the radial Poisson equation.  For the explicit
difference of two kernel scales, the primitive is nonnegative before the
larger support radius and vanishes after it.

No regularity at the origin is asserted in this file.
-/

open Set MeasureTheory
open scoped Interval Topology

namespace PshLines.Regularization.RadialPoissonPrimitive

open RadialPoissonCertificate
open RadialPoissonSlope
open RadialCumulativeSign
open RadialPolarMass

/-- The radial Poisson primitive, normalized to vanish at the reference
squared radius `A`.-/
noncomputable def radialPoissonPrimitive
    (n : ℕ) (g : ℝ → ℝ) (A s : ℝ) : ℝ :=
  ∫ t in A..s, radialPoissonSlope n g t

/--
@isnad1 id=eq.0h3v.s4.070298937954 from=translated src=- shape=4c60304c vocab=2a3f2d71
-/
@[simp]
theorem radialPoissonPrimitive_self
    (n : ℕ) (g : ℝ → ℝ) (A : ℝ) :
    radialPoissonPrimitive n g A A = 0 := by
  simp [radialPoissonPrimitive]

/-- The radial Poisson slope is continuous on the positive half-line.
@isnad1 id=continuo.2h2v.s5.5c6977012cf8 from=translated src=- shape=bd6750b7 vocab=f896e7df
-/
theorem radialPoissonSlope_continuousOn_Ioi
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (radialPoissonSlope n g) (Ioi 0) := by
  intro s hs
  exact (radialPoissonSlope_hasDerivAt hn hg hs).continuousAt.continuousWithinAt

/-- On the positive half-line, differentiating the primitive recovers the
radial Poisson slope.
@isnad1 id=hasderiv.4h4v.s6.ef2f70d89813 from=translated src=- shape=d1084cb3 vocab=552a7239
-/
theorem radialPoissonPrimitive_hasDerivAt
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    HasDerivAt (radialPoissonPrimitive n g A)
      (radialPoissonSlope n g s) s := by
  have hsub : uIcc A s ⊆ Ioi (0 : ℝ) := by
    simp [uIcc, Icc_subset_Ioi_iff, hA, hs]
  have hcont := radialPoissonSlope_continuousOn_Ioi hn hg
  have hint : IntervalIntegrable (radialPoissonSlope n g) volume A s :=
    (hcont.mono hsub).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (radialPoissonSlope n g) (𝓝 s) :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi s hs
  have hconts : ContinuousAt (radialPoissonSlope n g) s :=
    isOpen_Ioi.continuousOn_iff.mp hcont hs
  unfold radialPoissonPrimitive
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hconts

/-- The derivative of the primitive is itself differentiable away from the
origin, with the quotient-rule derivative of the radial slope.
@isnad1 id=hasderiv.4h4v.s7.2adb9a784689 from=translated src=- shape=2aa25172 vocab=f4c49ae6
-/
theorem radialPoissonPrimitive_deriv_hasDerivAt
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    HasDerivAt (deriv (radialPoissonPrimitive n g A))
      (g s / (4 * s) -
        (n : ℝ) * radialPoissonSlope n g s / s) s := by
  apply (radialPoissonSlope_hasDerivAt hn hg hs).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact (radialPoissonPrimitive_hasDerivAt hn hg hA ht).deriv

/-- The radial primitive satisfies the second-order one-variable Poisson
equation on the positive half-line.
@isnad1 id=eq.4h4v.s7.65d1a8bec0cc from=translated src=- shape=34f8bee3 vocab=b2f045c5
-/
theorem radialPoissonPrimitive_ode
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    4 * (s * deriv (deriv (radialPoissonPrimitive n g A)) s +
      (n : ℝ) * deriv (radialPoissonPrimitive n g A) s) = g s := by
  rw [(radialPoissonPrimitive_deriv_hasDerivAt hn hg hA hs).deriv,
    (radialPoissonPrimitive_hasDerivAt hn hg hA hs).deriv]
  field_simp
  ring

/-- If the radial slope is nonpositive between `s` and the normalization
radius `A`, then the primitive is nonnegative at `s`.
@isnad1 id=le.2h4v.s5.3478aeeb6ac3 from=translated src=- shape=9ab73046 vocab=31eb9d34
-/
theorem radialPoissonPrimitive_nonneg
    {n : ℕ} {g : ℝ → ℝ} {A s : ℝ} (hsA : s ≤ A)
    (hslope : ∀ t ∈ Icc s A, radialPoissonSlope n g t ≤ 0) :
    0 ≤ radialPoissonPrimitive n g A s := by
  calc
    radialPoissonPrimitive n g A s =
        ∫ t in s..A, -radialPoissonSlope n g t := by
      rw [radialPoissonPrimitive, intervalIntegral.integral_symm,
        intervalIntegral.integral_neg]
    _ ≥ 0 := intervalIntegral.integral_nonneg hsA fun t ht =>
      neg_nonneg.mpr (hslope t ht)

/-- If the slope vanishes at and beyond the normalization radius, then the
primitive vanishes there as well.
@isnad1 id=eq.2h4v.s5.a915429efbfd from=translated src=- shape=46d90ac6 vocab=21557f32
-/
theorem radialPoissonPrimitive_eq_zero_of_slope_eq_zero
    {n : ℕ} {g : ℝ → ℝ} {A s : ℝ} (hAs : A ≤ s)
    (hzero : ∀ t, A ≤ t → radialPoissonSlope n g t = 0) :
    radialPoissonPrimitive n g A s = 0 := by
  unfold radialPoissonPrimitive
  calc
    (∫ t in A..s, radialPoissonSlope n g t) = ∫ _t in A..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc A s := (uIcc_of_le hAs).symm ▸ ht
      exact hzero t ht'.1
    _ = 0 := by simp

/-- If a weighted radial datum is integrable on the positive half-line, has
zero total weighted mass, and vanishes after `A`, then its weighted cumulative
term vanishes at every `s ≥ A`.
@isnad1 id=eq.5h4v.s7.0232e54abe84 from=translated src=- shape=3027f10d vocab=846e79ad
-/
theorem radialWeightedCumulative_eq_zero_of_total_and_outer_zero
    {n : ℕ} {g : ℝ → ℝ} {A s : ℝ} (hA : 0 < A) (hAs : A ≤ s)
    (hint : IntegrableOn (fun t : ℝ => t ^ (n - 1) * g t) (Ioi 0))
    (htotal : ∫ t in Ioi (0 : ℝ), t ^ (n - 1) * g t = 0)
    (hzero : ∀ t, A < t → g t = 0) :
    radialWeightedCumulative n g s = 0 := by
  let f : ℝ → ℝ := fun t => t ^ (n - 1) * g t
  have hs : 0 ≤ s := hA.le.trans hAs
  have hintS : IntegrableOn f (Ioi s) :=
    hint.mono_set (Ioi_subset_Ioi hs)
  have htail : ∫ t in Ioi s, f t = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    dsimp [f]
    rw [hzero t (hAs.trans_lt ht), mul_zero]
  have hadd := intervalIntegral.integral_interval_add_Ioi
    (a := (0 : ℝ)) (b := s) hint hintS
  rw [htail, add_zero, htotal] at hadd
  rw [radialWeightedCumulative]
  exact hadd

/-- The explicit kernel difference has a nonpositive Poisson slope whenever
the scale index increases.
@isnad1 id=le.4h5v.s6.1a6a413809b9 from=translated src=- shape=f9146618 vocab=20715287
-/
theorem radialPoissonSlope_explicitRadialKernelSqDifference_nonpos
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ} (hs : 0 < s) :
    radialPoissonSlope n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s ≤ 0 :=
  radialPoissonSlope_nonpos hs
    (radialWeightedCumulative_explicitRadialKernelSqDifference_nonpos
      hn R hR hab hs.le)

/-- Before the normalization radius, the primitive associated to an
increasing pair of kernel scales is nonnegative.
@isnad1 id=le.5h6v.s6.84be284b48e4 from=translated src=- shape=da6a84d4 vocab=3fd8dc2e
-/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_nonneg
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {A s : ℝ}
    (hs : 0 < s) (hsA : s ≤ A) :
    0 ≤ radialPoissonPrimitive n
      (explicitRadialKernelSqDifference (n := n) R hR a b) A s := by
  apply radialPoissonPrimitive_nonneg hsA
  intro t ht
  exact radialPoissonSlope_explicitRadialKernelSqDifference_nonpos
    hn R hR hab (hs.trans_le ht.1)

/-- The weighted cumulative term of the explicit kernel difference vanishes
at and beyond the squared outer radius of the larger-support scale.
@isnad1 id=eq.4h5v.s6.8e1175f0e852 from=translated src=- shape=a194c688 vocab=57585b39
-/
theorem radialWeightedCumulative_explicitRadialKernelSqDifference_eq_zero_of_outer
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    radialWeightedCumulative n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s = 0 := by
  let A : ℝ := (R / ((a : ℝ) + 1)) ^ 2
  let g : ℝ → ℝ :=
    explicitRadialKernelSqDifference (n := n) R hR a b
  let f : ℝ → ℝ := fun t => t ^ (n - 1) * g t
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hfcont : Continuous f :=
    (continuous_id.pow _).mul
      (explicitRadialKernelSqDifference_contDiff R hR a b).continuous
  have hleft : IntegrableOn f (Ioc 0 A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mp
      (hfcont.intervalIntegrable 0 A)
  have hright : IntegrableOn f (Ioi A) := by
    apply integrableOn_zero.congr_fun
    · intro t ht
      dsimp [f, g]
      rw [explicitRadialKernelSqDifference_eq_zero_of_sq_rOut_le
        R hR hab ht.le, mul_zero]
    · exact measurableSet_Ioi
  have hint : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hA.le]
    exact hleft.union hright
  apply radialWeightedCumulative_eq_zero_of_total_and_outer_zero
    hA hs hint
  · exact integral_explicitRadialKernelSqDifference_weighted_eq_zero
      hn R hR a b
  · intro t ht
    exact explicitRadialKernelSqDifference_eq_zero_of_sq_rOut_le
      R hR hab ht.le

/-- The explicit Poisson slope vanishes at and beyond the squared outer
radius of the larger-support scale.
@isnad1 id=eq.4h5v.s6.4bf61f156e86 from=translated src=- shape=a194c688 vocab=b1db8492
-/
theorem radialPoissonSlope_explicitRadialKernelSqDifference_eq_zero_of_outer
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    radialPoissonSlope n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s = 0 := by
  rw [radialPoissonSlope,
    radialWeightedCumulative_explicitRadialKernelSqDifference_eq_zero_of_outer
      hn R hR hab hs,
    zero_div]

/-- With the reference point chosen at the exact squared outer radius, the
explicit primitive vanishes everywhere outside that radius.
@isnad1 id=eq.4h5v.s7.65af139d6f1d from=translated src=- shape=e8b16d04 vocab=48cae86f
-/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_eq_zero_of_outer
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    radialPoissonPrimitive n
      (explicitRadialKernelSqDifference (n := n) R hR a b)
      ((R / ((a : ℝ) + 1)) ^ 2) s = 0 := by
  apply radialPoissonPrimitive_eq_zero_of_slope_eq_zero hs
  intro t ht
  exact radialPoissonSlope_explicitRadialKernelSqDifference_eq_zero_of_outer
    hn R hR hab ht

end PshLines.Regularization.RadialPoissonPrimitive
