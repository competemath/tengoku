import Tengoku.PshdLean.PshLines.Regularization.RadialPoissonPrimitive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Removing the origin singularity after radial integration

The quotient defining `radialPoissonSlope` has value zero at the origin,
because Lean's division sends `0 / 0` to zero.  When the radial datum is
constant near the origin, its punctured value instead has a generally
nonzero limit.  We therefore leave the slope unchanged and introduce a
single-point modification only as a proof device.  Interval integration is
insensitive to that modification.

For the explicit kernel difference the squared-radius datum is constant on a
full interval to the left of a positive number.  The modified slope is then
globally smooth, the original primitive is affine near zero, and the
primitive is globally smooth.
-/

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace PshLines.Regularization.RadialPoissonOrigin

open RadialPoissonCertificate
open RadialPoissonSlope
open RadialPoissonPrimitive
open FirstPass

/-! ## Generic removable-origin calculus -/

/-- A locally constant radial datum has the expected elementary weighted
cumulative integral.  The hypothesis is deliberately one-sided: the
applications are constant on all `s < δ`, including every negative input.
@isnad1 id=eq.4h5v.s6.60ffa7edd4a5 from=translated src=- shape=cb741024 vocab=6f72848c
-/
theorem radialWeightedCumulative_eq_const_mul_pow
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} {c δ s : ℝ}
    (hδ : 0 < δ) (hs : s < δ) (hg : ∀ t, t < δ → g t = c) :
    radialWeightedCumulative n g s = c * s ^ n / (n : ℝ) := by
  have hmax : max 0 s < δ := max_lt hδ hs
  unfold radialWeightedCumulative
  calc
    (∫ t in 0..s, t ^ (n - 1) * g t) =
        ∫ t in 0..s, c * t ^ (n - 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htδ : t < δ :=
        ht.2.trans_lt hmax
      change t ^ (n - 1) * g t = c * t ^ (n - 1)
      rw [hg t htδ]
      ring
    _ = c * ∫ t in 0..s, t ^ (n - 1) := by
      rw [intervalIntegral.integral_const_mul]
    _ = c * s ^ n / (n : ℝ) := by
      rw [integral_pow]
      have hn' : n - 1 + 1 = n := by omega
      rw [hn']
      have hncast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        exact_mod_cast hn'
      rw [hncast, zero_pow hn.ne']
      ring

/-- Away from zero, the apparent quotient singularity has the constant value
forced by a locally constant radial datum.
@isnad1 id=eq.5h5v.s6.655b58a9797a from=translated src=- shape=ea8c2256 vocab=75e3b762
-/
theorem radialPoissonSlope_eq_const_div
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} {c δ s : ℝ}
    (hδ : 0 < δ) (hs : s < δ) (hs0 : s ≠ 0)
    (hg : ∀ t, t < δ → g t = c) :
    radialPoissonSlope n g s = c / (4 * (n : ℝ)) := by
  rw [radialPoissonSlope,
    radialWeightedCumulative_eq_const_mul_pow hn hδ hs hg]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsn : s ^ n ≠ 0 := pow_ne_zero n hs0
  field_simp

/-- The removable extension changes the radial slope only at the origin.-/
noncomputable def radialPoissonSlopeExtension
    (n : ℕ) (g : ℝ → ℝ) (c : ℝ) (s : ℝ) : ℝ :=
  if s = 0 then c / (4 * (n : ℝ)) else radialPoissonSlope n g s

/--
@isnad1 id=eq.1h4v.s4.38809995652d from=translated src=- shape=c1bda47d vocab=406c5b00
-/
theorem radialPoissonSlopeExtension_eq_of_ne
    {n : ℕ} {g : ℝ → ℝ} {c s : ℝ} (hs : s ≠ 0) :
    radialPoissonSlopeExtension n g c s = radialPoissonSlope n g s := by
  simp [radialPoissonSlopeExtension, hs]

/--
@isnad1 id=eq.0h3v.s5.dec5e202bc97 from=translated src=- shape=652584bd vocab=32e76075
-/
@[simp]
theorem radialPoissonSlopeExtension_zero
    (n : ℕ) (g : ℝ → ℝ) (c : ℝ) :
    radialPoissonSlopeExtension n g c 0 = c / (4 * (n : ℝ)) := by
  simp [radialPoissonSlopeExtension]

/-- The single-point extension is constant throughout the flat region.
@isnad1 id=eq.4h5v.s6.21d3158443a2 from=translated src=- shape=6d300753 vocab=7b2bc5ff
-/
theorem radialPoissonSlopeExtension_eq_const_div
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} {c δ s : ℝ}
    (hδ : 0 < δ) (hs : s < δ)
    (hg : ∀ t, t < δ → g t = c) :
    radialPoissonSlopeExtension n g c s = c / (4 * (n : ℝ)) := by
  by_cases hs0 : s = 0
  · subst s
    simp
  · rw [radialPoissonSlopeExtension_eq_of_ne hs0,
      radialPoissonSlope_eq_const_div hn hδ hs hs0 hg]

/-- A smooth datum has a smooth weighted cumulative term.
@isnad1 id=contdiff.1h2v.s6.a7dfe4e4d001 from=translated src=- shape=57d4b327 vocab=8dc425e7
-/
theorem radialWeightedCumulative_contDiff
    {n : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (radialWeightedCumulative n g) := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · intro s
    exact (radialWeightedCumulative_hasDerivAt hg.continuous s).differentiableAt
  · have hderiv : deriv (radialWeightedCumulative n g) =
        fun s => s ^ (n - 1) * g s := by
      funext s
      exact (radialWeightedCumulative_hasDerivAt hg.continuous s).deriv
    rw [hderiv]
    exact (contDiff_id.pow _).mul hg

/-- Once the origin value is repaired, a smooth datum which is constant below
a positive threshold gives a globally smooth radial slope.
@isnad1 id=contdiff.4h4v.s6.c61e27dc84f7 from=translated src=- shape=9a601a7f vocab=f1fc2516
-/
theorem radialPoissonSlopeExtension_contDiff
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {c δ : ℝ} (hδ : 0 < δ)
    (hconst : ∀ s, s < δ → g s = c) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPoissonSlopeExtension n g c) := by
  have hleft : ContDiffOn ℝ (⊤ : ℕ∞)
      (radialPoissonSlopeExtension n g c) (Iio δ) := by
    apply contDiff_const.contDiffOn.congr
    intro s hs
    exact (radialPoissonSlopeExtension_eq_const_div
      hn hδ hs hconst)
  have hright : ContDiffOn ℝ (⊤ : ℕ∞)
      (radialPoissonSlopeExtension n g c) (Ioi 0) := by
    have hnum : ContDiffOn ℝ (⊤ : ℕ∞)
        (radialWeightedCumulative n g) (Ioi 0) :=
      (radialWeightedCumulative_contDiff (n := n) hg).contDiffOn
    have hden : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun s : ℝ => 4 * s ^ n) (Ioi 0) :=
      (contDiff_const.mul (contDiff_id.pow n)).contDiffOn
    have hquot : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun s : ℝ => radialWeightedCumulative n g s / (4 * s ^ n))
        (Ioi 0) :=
      hnum.div hden fun s hs =>
        mul_ne_zero (by norm_num) (pow_ne_zero n hs.ne')
    apply hquot.congr
    intro s hs
    have hspos : 0 < s := hs
    have hs0 : s ≠ 0 := hspos.ne'
    simp [radialPoissonSlopeExtension, radialPoissonSlope, hs0]
  apply contDiff_of_contDiffOn_union_of_isOpen hleft hright
  · apply Set.eq_univ_of_forall
    intro s
    by_cases hs : s < δ
    · exact Or.inl hs
    · exact Or.inr (hδ.trans_le (le_of_not_gt hs))
  · exact isOpen_Iio
  · exact isOpen_Ioi

/-- Interval integration cannot detect the value changed at the origin.
@isnad1 id=eq.0h5v.s5.6e33808731be from=translated src=- shape=3895675c vocab=649f1ec8
-/
theorem integral_radialPoissonSlope_eq_extension
    (n : ℕ) (g : ℝ → ℝ) (c A s : ℝ) :
    (∫ t in A..s, radialPoissonSlope n g t) =
      ∫ t in A..s, radialPoissonSlopeExtension n g c t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht0
  intro _ht
  exact (radialPoissonSlopeExtension_eq_of_ne ht0).symm

/-- In the flat region the original primitive is exactly affine.  This also
records explicitly why the exceptional value of the slope at zero is
harmless: it disappears under interval integration.
@isnad1 id=eq.5h6v.s7.1908578e15b5 from=translated src=- shape=bfeecde1 vocab=28b1015d
-/
theorem radialPoissonPrimitive_eq_affine_of_lt
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {c δ A s : ℝ} (hδ : 0 < δ)
    (hs : s < δ) (hconst : ∀ t, t < δ → g t = c) :
    radialPoissonPrimitive n g A s =
      radialPoissonPrimitive n g A 0 + c / (4 * (n : ℝ)) * s := by
  let q : ℝ → ℝ := radialPoissonSlopeExtension n g c
  have hqcont : Continuous q :=
    (radialPoissonSlopeExtension_contDiff hn hg hδ hconst).continuous
  have hA0 : IntervalIntegrable q volume A 0 :=
    hqcont.intervalIntegrable A 0
  have h0s : IntervalIntegrable q volume 0 s :=
    hqcont.intervalIntegrable 0 s
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA0 h0s
  calc
    radialPoissonPrimitive n g A s = ∫ t in A..s, q t := by
      rw [radialPoissonPrimitive]
      exact integral_radialPoissonSlope_eq_extension n g c A s
    _ = (∫ t in A..0, q t) + ∫ t in 0..s, q t := hsplit.symm
    _ = radialPoissonPrimitive n g A 0 +
        ∫ _t in 0..s, c / (4 * (n : ℝ)) := by
      congr 1
      · rw [radialPoissonPrimitive]
        exact (integral_radialPoissonSlope_eq_extension n g c A 0).symm
      · apply intervalIntegral.integral_congr
        intro t ht
        have htδ : t < δ :=
          ht.2.trans_lt (max_lt hδ hs)
        exact radialPoissonSlopeExtension_eq_const_div hn hδ htδ hconst
    _ = radialPoissonPrimitive n g A 0 +
        c / (4 * (n : ℝ)) * s := by
      simp [intervalIntegral.integral_const]
      ring

/-- Radial integration removes the origin singularity completely: under the
flat-origin hypothesis, the original (unmodified) primitive is globally
smooth.
@isnad1 id=contdiff.4h5v.s6.0f106c3e7f1e from=translated src=- shape=fbb00e63 vocab=fee5b572
-/
theorem radialPoissonPrimitive_contDiff_of_eq_const_below
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {c δ A : ℝ} (hδ : 0 < δ)
    (hconst : ∀ s, s < δ → g s = c) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPoissonPrimitive n g A) := by
  let q : ℝ → ℝ := radialPoissonSlopeExtension n g c
  let F : ℝ → ℝ := fun s => ∫ t in A..s, q t
  have hq : ContDiff ℝ (⊤ : ℕ∞) q :=
    radialPoissonSlopeExtension_contDiff hn hg hδ hconst
  have hFderiv : ∀ s, HasDerivAt F (q s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hq.continuous.intervalIntegrable A s)
      hq.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hq.continuous.continuousAt
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    rw [contDiff_infty_iff_deriv]
    constructor
    · exact fun s => (hFderiv s).differentiableAt
    · have hderiv : deriv F = q := by
        funext s
        exact (hFderiv s).deriv
      rw [hderiv]
      exact hq
  have heq : radialPoissonPrimitive n g A = F := by
    funext s
    rw [radialPoissonPrimitive]
    exact integral_radialPoissonSlope_eq_extension n g c A s
  rw [heq]
  exact hFsmooth

/-! ## The explicit kernel difference -/

/-- The explicit squared-radius difference is constant throughout a genuine
neighborhood of the origin.
@isnad1 id=eq.2h5v.s8.348e38db6e5f from=translated src=- shape=51fc21cf vocab=2b2045fc
-/
theorem explicitRadialKernelSqDifference_eq_origin_of_lt_min_rIn_sq
    {n : ℕ} (R : ℝ) (hR : 0 < R) (a b : ℕ) {s : ℝ}
    (hs : s < min
      ((shrinkingBump (E := ComplexModel n) R hR a).rIn ^ 2)
      ((shrinkingBump (E := ComplexModel n) R hR b).rIn ^ 2)) :
    explicitRadialKernelSqDifference (n := n) R hR a b s =
      explicitRadialKernelSqDifference (n := n) R hR a b 0 := by
  have hsa : s < (shrinkingBump (E := ComplexModel n) R hR a).rIn ^ 2 :=
    hs.trans_le (min_le_left _ _)
  have hsb : s < (shrinkingBump (E := ComplexModel n) R hR b).rIn ^ 2 :=
    hs.trans_le (min_le_right _ _)
  have h0a : (0 : ℝ) <
      (shrinkingBump (E := ComplexModel n) R hR a).rIn ^ 2 := by
    exact sq_pos_of_pos
      (shrinkingBump (E := ComplexModel n) R hR a).rIn_pos
  have h0b : (0 : ℝ) <
      (shrinkingBump (E := ComplexModel n) R hR b).rIn ^ 2 := by
    exact sq_pos_of_pos
      (shrinkingBump (E := ComplexModel n) R hR b).rIn_pos
  rw [explicitRadialKernelSqDifference,
    explicitRadialKernelSqDifference,
    explicitRadialKernelSqProfile,
    explicitRadialKernelSqProfile,
    explicitRadialKernelSqProfile,
    explicitRadialKernelSqProfile,
    explicitRadialRawSqProfile_eq_one_of_lt_sq_rIn R hR a hsa,
    explicitRadialRawSqProfile_eq_one_of_lt_sq_rIn R hR b hsb,
    explicitRadialRawSqProfile_eq_one_of_lt_sq_rIn R hR a h0a,
    explicitRadialRawSqProfile_eq_one_of_lt_sq_rIn R hR b h0b]

/-- On its flat-origin interval, the explicit Poisson primitive is the
affine function with the removable limiting slope.
@isnad1 id=eq.3h6v.s8.80b88621b370 from=translated src=- shape=1e51ebd5 vocab=5bd9f932
-/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_eq_affine
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    (a b : ℕ) (A : ℝ) {s : ℝ}
    (hs : s < min
      ((shrinkingBump (E := ComplexModel n) R hR a).rIn ^ 2)
      ((shrinkingBump (E := ComplexModel n) R hR b).rIn ^ 2)) :
    radialPoissonPrimitive n
        (explicitRadialKernelSqDifference (n := n) R hR a b) A s =
      radialPoissonPrimitive n
          (explicitRadialKernelSqDifference (n := n) R hR a b) A 0 +
        explicitRadialKernelSqDifference (n := n) R hR a b 0 /
          (4 * (n : ℝ)) * s := by
  apply radialPoissonPrimitive_eq_affine_of_lt
    (c := explicitRadialKernelSqDifference (n := n) R hR a b 0)
    hn (explicitRadialKernelSqDifference_contDiff R hR a b)
  · exact lt_min
      (sq_pos_of_pos
        (shrinkingBump (E := ComplexModel n) R hR a).rIn_pos)
      (sq_pos_of_pos
        (shrinkingBump (E := ComplexModel n) R hR b).rIn_pos)
  · exact hs
  · intro t ht
    exact explicitRadialKernelSqDifference_eq_origin_of_lt_min_rIn_sq
      R hR a b ht

/-- The Poisson primitive of an explicit pair of kernel scales is globally
smooth across the origin.
@isnad1 id=contdiff.2h5v.s6.a2784bb9b84d from=translated src=- shape=539262fa vocab=b59c4e51
-/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_contDiff
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    (a b : ℕ) (A : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (radialPoissonPrimitive n
        (explicitRadialKernelSqDifference (n := n) R hR a b) A) := by
  let δ : ℝ := min
    ((shrinkingBump (E := ComplexModel n) R hR a).rIn ^ 2)
    ((shrinkingBump (E := ComplexModel n) R hR b).rIn ^ 2)
  let g : ℝ → ℝ :=
    explicitRadialKernelSqDifference (n := n) R hR a b
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min
      (sq_pos_of_pos
        (shrinkingBump (E := ComplexModel n) R hR a).rIn_pos)
      (sq_pos_of_pos
        (shrinkingBump (E := ComplexModel n) R hR b).rIn_pos)
  apply radialPoissonPrimitive_contDiff_of_eq_const_below
    hn (explicitRadialKernelSqDifference_contDiff R hR a b) hδ
  intro s hs
  exact explicitRadialKernelSqDifference_eq_origin_of_lt_min_rIn_sq
    R hR a b hs

/-- In particular, the explicit primitive is smooth at the origin.
@isnad1 id=contdiff.2h5v.s6.4d39e0b80838 from=translated src=- shape=9d5319d6 vocab=10714621
-/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_contDiffAt_zero
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    (a b : ℕ) (A : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (radialPoissonPrimitive n
        (explicitRadialKernelSqDifference (n := n) R hR a b) A) 0 :=
  (radialPoissonPrimitive_explicitRadialKernelSqDifference_contDiff
    hn R hR a b A).contDiffAt

end PshLines.Regularization.RadialPoissonOrigin
