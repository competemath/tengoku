import Tengoku.PshdLean.PshLines.Regularization.HolomorphicPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Square-norm profiles for the explicit radial kernel

The explicit regularizing kernel is rewritten as a one-variable smooth profile
of the squared norm.  This is the first input needed for a radial Poisson
primitive whose complex Levi trace recovers differences of kernel scales.
-/

open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace PshLines.Regularization.RadialPoissonCertificate

open FirstPass
open HolomorphicPullback

variable {n : ℕ}

/-- The standard complex model has twice its complex dimension over `ℝ`.
@isnad1 id=eq.0h1v.s7.bdfab81f53a4 from=translated src=- shape=e96f2693 vocab=90ce0451
-/
theorem finrank_real_complexModel (n : ℕ) :
    Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexModel n),
    Complex.finrank_real_complex, finrank_euclideanSpace_fin]

/-- The one-variable squared-radius profile underlying `explicitRadialRaw`.
For nonpositive inputs `Real.sqrt` vanishes, so this definition also supplies
the constant extension across the origin that will make the profile smooth.-/
noncomputable def explicitRadialRawSqProfile
    (R : ℝ) (hR : 0 < R) (j : ℕ) (s : ℝ) : ℝ :=
  Real.smoothTransition
    ((2 - Real.sqrt s /
      (shrinkingBump (E := ComplexModel n) R hR j).rIn) / (2 - 1))

/-- The normalized one-variable squared-radius profile.-/
noncomputable def explicitRadialKernelSqProfile
    (R : ℝ) (hR : 0 < R) (j : ℕ) (s : ℝ) : ℝ :=
  explicitRadialRawSqProfile (n := n) R hR j s /
    ∫ y : ComplexModel n, explicitRadialRaw R hR j y

/-- The explicit raw radial kernel is its squared-radius profile evaluated at
the squared norm.
@isnad1 id=eq.1h4v.s6.810317111923 from=translated src=- shape=c35442a7 vocab=9fa17554
-/
theorem explicitRadialRaw_eq_sqProfile_norm_sq
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel n) :
    explicitRadialRaw R hR j x =
      explicitRadialRawSqProfile (n := n) R hR j (‖x‖ ^ 2) := by
  simp [explicitRadialRaw, explicitRadialRawSqProfile,
    ContDiffBumpBase.ofInnerProductSpace, norm_smul, Real.norm_eq_abs,
    abs_of_pos (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos,
    Real.sqrt_sq (norm_nonneg x), div_eq_mul_inv, mul_comm]

/-- The normalized explicit kernel is its normalized squared-radius profile.
@isnad1 id=eq.1h4v.s6.a2b893490987 from=translated src=- shape=c35442a7 vocab=e20bf65c
-/
theorem explicitRadialKernel_eq_sqProfile_norm_sq
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel n) :
    explicitRadialKernel R hR j x =
      explicitRadialKernelSqProfile (n := n) R hR j (‖x‖ ^ 2) := by
  rw [explicitRadialKernel, explicitRadialKernelSqProfile,
    explicitRadialRaw_eq_sqProfile_norm_sq]

/-- The squared-radius profile is already constant on a full neighborhood of
the origin.  This is the flat region that removes the apparent singularity of
the square root at zero.
@isnad1 id=eq.2h4v.s7.05d8f5eeda3f from=translated src=- shape=2780aa2b vocab=6b9c156c
-/
theorem explicitRadialRawSqProfile_eq_one_of_lt_sq_rIn
    (R : ℝ) (hR : 0 < R) (j : ℕ) {s : ℝ}
    (hs : s <
      (shrinkingBump (E := ComplexModel n) R hR j).rIn ^ 2) :
    explicitRadialRawSqProfile (n := n) R hR j s = 1 := by
  rw [explicitRadialRawSqProfile]
  apply Real.smoothTransition.one_of_one_le
  norm_num
  have hsqrt : Real.sqrt s <
      (shrinkingBump (E := ComplexModel n) R hR j).rIn :=
    (Real.sqrt_lt'
      (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos).2 hs
  have hdiv : Real.sqrt s /
      (shrinkingBump (E := ComplexModel n) R hR j).rIn ≤ 1 :=
    ((div_lt_one
      (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos).2 hsqrt).le
  linarith

/-- The raw squared-radius profile is globally smooth.  On the open set below
the square of the inner radius it is constant; on the positive half-line it
is a smooth composite with `Real.sqrt`.  These two open sets cover `ℝ`.
@isnad1 id=contdiff.1h3v.s5.f27a526f6f69 from=translated src=- shape=379d7daf vocab=d237569a
-/
theorem explicitRadialRawSqProfile_contDiff
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (explicitRadialRawSqProfile (n := n) R hR j) := by
  let r : ℝ := (shrinkingBump (E := ComplexModel n) R hR j).rIn
  have hr : 0 < r :=
    (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos
  have hleft : ContDiffOn ℝ (⊤ : ℕ∞)
      (explicitRadialRawSqProfile (n := n) R hR j) (Iio (r ^ 2)) := by
    apply contDiff_const.contDiffOn.congr
    intro s hs
    exact explicitRadialRawSqProfile_eq_one_of_lt_sq_rIn R hR j hs
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) Real.sqrt (Ioi 0) :=
    contDiff_id.contDiffOn.sqrt (fun s hs => ne_of_gt hs)
  have hright : ContDiffOn ℝ (⊤ : ℕ∞)
      (explicitRadialRawSqProfile (n := n) R hR j) (Ioi 0) := by
    rw [show explicitRadialRawSqProfile (n := n) R hR j =
        fun s => Real.smoothTransition
          ((2 - Real.sqrt s / r) / (2 - 1)) by
      funext s
      rfl]
    exact Real.smoothTransition.contDiff.comp_contDiffOn
      ((contDiff_const.contDiffOn.sub (hsqrt.div_const r)).div_const (2 - 1))
  apply contDiff_of_contDiffOn_union_of_isOpen hleft hright
  · apply Set.eq_univ_of_forall
    intro s
    by_cases hs : s < r ^ 2
    · exact Or.inl hs
    · exact Or.inr (lt_of_lt_of_le (sq_pos_of_pos hr) (le_of_not_gt hs))
  · exact isOpen_Iio
  · exact isOpen_Ioi

/-- Normalization by the positive total mass preserves global smoothness.
@isnad1 id=contdiff.1h3v.s5.bdcd368bb6d9 from=translated src=- shape=379d7daf vocab=d70fc4fc
-/
theorem explicitRadialKernelSqProfile_contDiff
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (explicitRadialKernelSqProfile (n := n) R hR j) :=
  (explicitRadialRawSqProfile_contDiff R hR j).div_const _

/-- The squared-radius profile of the difference between two normalized
kernel scales.-/
noncomputable def explicitRadialKernelSqDifference
    (R : ℝ) (hR : 0 < R) (a b : ℕ) (s : ℝ) : ℝ :=
  explicitRadialKernelSqProfile (n := n) R hR a s -
    explicitRadialKernelSqProfile (n := n) R hR b s

/-- A difference of kernel profiles is globally smooth.
@isnad1 id=contdiff.1h4v.s5.678947629f75 from=translated src=- shape=29f2a553 vocab=2670d8c1
-/
theorem explicitRadialKernelSqDifference_contDiff
    (R : ℝ) (hR : 0 < R) (a b : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (explicitRadialKernelSqDifference (n := n) R hR a b) :=
  (explicitRadialKernelSqProfile_contDiff R hR a).sub
    (explicitRadialKernelSqProfile_contDiff R hR b)

/-- The spatial difference of two normalized radial kernels is the
corresponding one-variable profile evaluated at the squared norm.
@isnad1 id=eq.1h5v.s6.c785867adfdc from=translated src=- shape=4436f2a8 vocab=dbb4cb6e
-/
theorem explicitRadialKernel_sub_eq_sqDifference_norm_sq
    (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : ComplexModel n) :
    explicitRadialKernel R hR a x - explicitRadialKernel R hR b x =
      explicitRadialKernelSqDifference (n := n) R hR a b (‖x‖ ^ 2) := by
  rw [explicitRadialKernelSqDifference,
    explicitRadialKernel_eq_sqProfile_norm_sq,
    explicitRadialKernel_eq_sqProfile_norm_sq]

/-- The raw squared-radius profile vanishes at and beyond its exact squared
outer radius.
@isnad1 id=eq.2h4v.s6.188d13f9de3b from=translated src=- shape=aeac1a68 vocab=8fd31a85
-/
theorem explicitRadialRawSqProfile_eq_zero_of_sq_rOut_le
    (R : ℝ) (hR : 0 < R) (j : ℕ) {s : ℝ}
    (hs : (R / ((j : ℝ) + 1)) ^ 2 ≤ s) :
    explicitRadialRawSqProfile (n := n) R hR j s = 0 := by
  rw [explicitRadialRawSqProfile, Real.smoothTransition.zero_iff_nonpos]
  norm_num
  have hrOut : 0 < R / ((j : ℝ) + 1) := by positivity
  have hsqrt : R / ((j : ℝ) + 1) ≤ Real.sqrt s :=
    (Real.le_sqrt' hrOut).2 hs
  have hratio := shrinkingBump_radius_ratio (E := ComplexModel n) R hR j
  have htwo : 2 * (shrinkingBump (E := ComplexModel n) R hR j).rIn ≤
      Real.sqrt s := by
    rw [← hratio]
    exact hsqrt
  have hdiv : (2 : ℝ) ≤ Real.sqrt s /
      (shrinkingBump (E := ComplexModel n) R hR j).rIn :=
    (le_div_iff₀
      (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos).2 htwo
  linarith

/-- Normalization does not change the exact outer vanishing threshold.
@isnad1 id=eq.2h4v.s6.a412124fb57e from=translated src=- shape=aeac1a68 vocab=cd21bb8a
-/
theorem explicitRadialKernelSqProfile_eq_zero_of_sq_rOut_le
    (R : ℝ) (hR : 0 < R) (j : ℕ) {s : ℝ}
    (hs : (R / ((j : ℝ) + 1)) ^ 2 ≤ s) :
    explicitRadialKernelSqProfile (n := n) R hR j s = 0 := by
  rw [explicitRadialKernelSqProfile,
    explicitRadialRawSqProfile_eq_zero_of_sq_rOut_le R hR j hs,
    zero_div]

/-- If `a ≤ b`, then the difference of scales `a` and `b` vanishes at and
beyond the larger, `a`-scale squared outer radius.
@isnad1 id=eq.3h5v.s6.4fb3216e4f1d from=translated src=- shape=9a4e73b2 vocab=afaf5b09
-/
theorem explicitRadialKernelSqDifference_eq_zero_of_sq_rOut_le
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    explicitRadialKernelSqDifference (n := n) R hR a b s = 0 := by
  have hden : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hab 1
  have hrad : R / ((b : ℝ) + 1) ≤ R / ((a : ℝ) + 1) :=
    div_le_div_of_nonneg_left hR.le (by positivity) hden
  have hsq : (R / ((b : ℝ) + 1)) ^ 2 ≤
      (R / ((a : ℝ) + 1)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hrad
  rw [explicitRadialKernelSqDifference,
    explicitRadialKernelSqProfile_eq_zero_of_sq_rOut_le R hR a hs,
    explicitRadialKernelSqProfile_eq_zero_of_sq_rOut_le R hR b (hsq.trans hs),
    sub_self]

/-! ## Generic radial cumulative calculus -/

/-- The cumulative term in the radial Poisson formula.  The exponent is
written with natural subtraction; the applications below use `0 < n`.-/
noncomputable def radialWeightedCumulative
    (n : ℕ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in 0..s, t ^ (n - 1) * g t

/--
@isnad1 id=eq.0h2v.s4.1de4b5392160 from=translated src=- shape=5918f7c5 vocab=7d1df521
-/
@[simp]
theorem radialWeightedCumulative_zero (n : ℕ) (g : ℝ → ℝ) :
    radialWeightedCumulative n g 0 = 0 := by
  simp [radialWeightedCumulative]

/-- The fundamental theorem of calculus for the weighted cumulative term.
@isnad1 id=hasderiv.1h3v.s6.169e7eed1dd3 from=translated src=- shape=a3c95016 vocab=aeda9b7c
-/
theorem radialWeightedCumulative_hasDerivAt
    {n : ℕ} {g : ℝ → ℝ} (hg : Continuous g) (s : ℝ) :
    HasDerivAt (radialWeightedCumulative n g)
      (s ^ (n - 1) * g s) s := by
  have hcont : Continuous (fun t : ℝ => t ^ (n - 1) * g t) :=
    (continuous_id.pow _).mul hg
  unfold radialWeightedCumulative
  convert intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 s)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt using 1

/-- A continuous radial datum has a continuous weighted cumulative term.
@isnad1 id=continuo.1h2v.s5.3b99250202ae from=translated src=- shape=c0999f8f vocab=0d91a4f5
-/
theorem radialWeightedCumulative_continuous
    {n : ℕ} {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (radialWeightedCumulative n g) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (radialWeightedCumulative_hasDerivAt hg s).continuousAt

/-- A continuous radial datum gives a `C¹` weighted cumulative term.
@isnad1 id=contdiff.1h2v.s5.92c701924bb7 from=translated src=- shape=5c656853 vocab=1949df9a
-/
theorem radialWeightedCumulative_contDiff_one
    {n : ℕ} {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (radialWeightedCumulative n g) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · exact fun s => (radialWeightedCumulative_hasDerivAt hg s).differentiableAt
  · have hderiv : deriv (radialWeightedCumulative n g) =
        fun s => s ^ (n - 1) * g s := by
      funext s
      exact (radialWeightedCumulative_hasDerivAt hg s).deriv
    rw [hderiv]
    exact (continuous_id.pow _).mul hg

/-- Convenience form when smoothness, rather than mere continuity, of the
radial datum is already available.
@isnad1 id=contdiff.1h2v.s6.b52668319979 from=translated src=- shape=03fde11b vocab=46a70ea6
-/
theorem radialWeightedCumulative_contDiff_one_of_contDiff
    {n : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ 1 (radialWeightedCumulative n g) :=
  radialWeightedCumulative_contDiff_one hg.continuous

end PshLines.Regularization.RadialPoissonCertificate
