/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.Bohr
import Tengoku.Seed.Algebra.Order.Archimedean.Basic
import Tengoku.Seed.Analysis.Calculus.BumpFunction.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dyadic kernels used in the positive estimate

This file records the elementary, exact part of the dyadic decomposition of
the quadratic Hilbert kernel.  The quotient defining a dyadic piece is given
the value zero at the origin; this is not an arbitrary extension, since the
numerator vanishes on a whole neighbourhood of the origin.
-/

open Function Set
open scoped ContDiff Topology

namespace QuadraticCarleson

/- The bump supplied by `ContDiffBump` is one on the inner closed ball and is
supported in the outer open ball.  With these radii those balls are exactly
the two intervals required in the paper. -/
noncomputable def dyadicCutoffData : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

noncomputable def dyadicCutoff : ℝ → ℝ := dyadicCutoffData

/--
@isnad1 id=contdiff.0h0v.s5.dcd4f08c70d9 from=translated src=- shape=3cea26be vocab=aaa32779
-/
theorem dyadicCutoff_smooth : ContDiff ℝ ∞ dyadicCutoff := by
  exact dyadicCutoffData.contDiff

/--
@isnad1 id=even.0h0v.s2.e2be5f41eb9c from=translated src=- shape=e3d48bcb vocab=ffc1f00d
-/
theorem dyadicCutoff_even : Function.Even dyadicCutoff := by
  intro x
  exact dyadicCutoffData.neg x

/--
@isnad1 id=le.0h1v.s3.5d6af0170a83 from=translated src=- shape=8a62b088 vocab=de6bdf80
-/
theorem dyadicCutoff_nonneg (x : ℝ) : 0 ≤ dyadicCutoff x := by
  exact dyadicCutoffData.nonneg

/--
@isnad1 id=le.0h1v.s3.3380a1c7e14e from=translated src=- shape=b14ee516 vocab=de6bdf80
-/
theorem dyadicCutoff_le_one (x : ℝ) : dyadicCutoff x ≤ 1 := by
  exact dyadicCutoffData.le_one

/--
@isnad1 id=eq.1h1v.s5.f8fb5ad8d735 from=translated src=- shape=7f1c967e vocab=5e6c5eab
-/
theorem dyadicCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1 / 4) :
    dyadicCutoff x = 1 := by
  apply dyadicCutoffData.one_of_mem_closedBall
  simpa [dyadicCutoffData, Metric.mem_closedBall, Real.dist_eq] using hx

/--
@isnad1 id=eq.1h1v.s5.bc051b7fdc52 from=translated src=- shape=f3a39d87 vocab=5e6c5eab
-/
theorem dyadicCutoff_eq_zero {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    dyadicCutoff x = 0 := by
  apply dyadicCutoffData.zero_of_le_dist
  simpa [dyadicCutoffData, Real.dist_eq] using hx

/--
@isnad1 id=le.0h0v.s5.6dfe75c2ba91 from=translated src=- shape=8a2e394f vocab=bb25e8fd
-/
theorem dyadicCutoff_support_subset :
    support dyadicCutoff ⊆ Ioo (-1 / 2 : ℝ) (1 / 2) := by
  change support (dyadicCutoffData : ℝ → ℝ) ⊆ _
  rw [dyadicCutoffData.support_eq]
  intro x hx
  have hx' : |x| < (1 / 2 : ℝ) := by
    simpa [dyadicCutoffData, Metric.mem_ball, Real.dist_eq] using hx
  rw [abs_lt] at hx'
  constructor <;> linarith

/-! The quotient extension at the singular point. -/
noncomputable def dyadicPsi (j : ℤ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else
    (dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)) / t

/--
@isnad1 id=eq.1h2v.s6.1b422ed9e918 from=translated src=- shape=6e90dd64 vocab=30e9b409
-/
theorem dyadicPsi_eq_quotient {j : ℤ} {t : ℝ} (ht : t ≠ 0) :
    dyadicPsi j t =
      (dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)) / t := by
  simp [dyadicPsi, ht]

/--
@isnad1 id=eq.0h1v.s4.136721b17af1 from=translated src=- shape=9b4d794a vocab=f2c7690b
-/
theorem dyadicPsi_zero (j : ℤ) : dyadicPsi j 0 = 0 := by
  simp [dyadicPsi]

/--
@isnad1 id=eq.1h2v.s5.06a848dbebf8 from=translated src=- shape=da25ebf4 vocab=1095cc83
-/
theorem dyadicPsi_eq_zero_of_abs_le {j : ℤ} {t : ℝ}
    (ht : |t| ≤ 2 ^ (j - 3 : ℤ)) : dyadicPsi j t = 0 := by
  by_cases ht0 : t = 0
  · simp [ht0, dyadicPsi]
  · rw [dyadicPsi_eq_quotient ht0]
    have hscale : |(2⁻¹ : ℝ) ^ (j - 1) * t| ≤ 1 / 4 := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      norm_num
      calc
        (1 / 2 : ℝ) ^ (j - 1) * |t| ≤
            (1 / 2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 3) :=
          mul_le_mul_of_nonneg_left ht
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) _))
        _ = 1 / 4 := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
    have hscale' : |(2⁻¹ : ℝ) ^ j * t| ≤ 1 / 4 := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      norm_num
      calc
        (1 / 2 : ℝ) ^ j * |t| ≤
            (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ (j - 3) :=
          mul_le_mul_of_nonneg_left ht
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) _))
        _ = 1 / 8 := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
        _ ≤ 1 / 4 := by norm_num
    rw [dyadicCutoff_eq_one hscale, dyadicCutoff_eq_one hscale']
    simp

/--
@isnad1 id=contdiff.0h2v.s5.bcbb79376d13 from=translated src=- shape=5c9e953d vocab=dde1c750
-/
theorem dyadicPsi_contDiffAt (j : ℤ) (t : ℝ) :
    ContDiffAt ℝ ∞ (dyadicPsi j) t := by
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hball : Metric.ball (0 : ℝ) (2 ^ (j - 3 : ℤ)) ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
    filter_upwards [hball] with u hu
    apply dyadicPsi_eq_zero_of_abs_le
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hu)
  · let q : ℝ → ℝ := fun u ↦
      (dyadicCutoff ((2⁻¹ : ℝ) ^ j * u) -
        dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * u)) / u
    have hq : ContDiffAt ℝ ∞ q t := by
      apply (ContDiffAt.sub ?_ ?_).div contDiffAt_id ht
      · exact dyadicCutoff_smooth.contDiffAt.comp t
          (contDiffAt_const.mul contDiffAt_id)
      · exact dyadicCutoff_smooth.contDiffAt.comp t
          (contDiffAt_const.mul contDiffAt_id)
    apply hq.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds ht] with u hu
    exact dyadicPsi_eq_quotient hu

/--
@isnad1 id=contdiff.0h1v.s5.92d3bc54d619 from=translated src=- shape=1e5679e5 vocab=6cc1830f
-/
theorem dyadicPsi_smooth : ∀ j : ℤ, ContDiff ℝ ∞ (dyadicPsi j) := by
  intro j
  rw [contDiff_iff_contDiffAt]
  exact dyadicPsi_contDiffAt j

/--
@isnad1 id=le.0h1v.s6.eea5760ffcf3 from=translated src=- shape=cffde610 vocab=082b03ce
-/
theorem dyadicPsi_support_subset (j : ℤ) :
    support (dyadicPsi j) ⊆ {t : ℝ | 2 ^ (j - 3 : ℤ) < |t| ∧
      |t| < 2 ^ (j - 1 : ℤ)} := by
  intro t ht
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h, dyadicPsi])
  have hinner : 2 ^ (j - 3 : ℤ) < |t| := by
    by_contra h
    exact ht (dyadicPsi_eq_zero_of_abs_le (le_of_not_gt h))
  have houter : |t| < 2 ^ (j - 1 : ℤ) := by
    by_contra h
    have hlarge : 2 ^ (j - 1 : ℤ) ≤ |t| := le_of_not_gt h
    have hfirst : 1 / 2 ≤ |(2⁻¹ : ℝ) ^ j * t| := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      calc
        (1 / 2 : ℝ) = (2⁻¹ : ℝ) ^ j * (2 : ℝ) ^ (j - 1) := by
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
        _ ≤
            (2⁻¹ : ℝ) ^ j * |t| :=
          mul_le_mul_of_nonneg_left hlarge
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _))
    have hsecond : 1 / 2 ≤ |(2⁻¹ : ℝ) ^ (j - 1) * t| := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      calc
        (1 / 2 : ℝ) ≤ 1 := by norm_num
        _ = (2⁻¹ : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1) := by
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
        _ ≤
            (2⁻¹ : ℝ) ^ (j - 1) * |t| :=
          mul_le_mul_of_nonneg_left hlarge
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _))
    have hzero : dyadicPsi j t = 0 := by
      rw [dyadicPsi_eq_quotient ht0]
      rw [dyadicCutoff_eq_zero hfirst, dyadicCutoff_eq_zero hsecond]
      simp
    exact ht hzero
  exact ⟨hinner, houter⟩

/--
@isnad1 id=odd.0h1v.s3.c5d28090fd64 from=translated src=- shape=8735051e vocab=b8a6f759
-/
theorem dyadicPsi_odd (j : ℤ) : Function.Odd (dyadicPsi j) := by
  intro t
  by_cases ht : t = 0
  · simp [ht, dyadicPsi]
  · rw [dyadicPsi_eq_quotient ht, dyadicPsi_eq_quotient (neg_ne_zero.mpr ht)]
    have harg₁ : (2⁻¹ : ℝ) ^ j * -t = -((2⁻¹ : ℝ) ^ j * t) := by ring
    have harg₂ : (2⁻¹ : ℝ) ^ (j - 1) * -t =
        -((2⁻¹ : ℝ) ^ (j - 1) * t) := by ring
    rw [harg₁, harg₂, dyadicCutoff_even, dyadicCutoff_even]
    simp only [div_neg]

/-! ## The paper's uniquely selected scale

For nonzero `lam` and `r ≥ 0`, the paper chooses the unique integer `j` for
which `2^r ≤ 2^j √|lam| < 2^(r+1)`.  We record both existence and
uniqueness, rather than hiding a rounding convention inside the definition.
-/

/-- The exact scale-selection inequalities in the positive proof.-/
def OscillatoryScaleSpec (lam : ℝ) (r : ℕ) (j : ℤ) : Prop :=
  (2 : ℝ) ^ r ≤ (2 : ℝ) ^ j * Real.sqrt |lam| ∧
    (2 : ℝ) ^ j * Real.sqrt |lam| < (2 : ℝ) ^ (r + 1)

private theorem oscillatoryScaleSpec_unique {lam : ℝ} {r : ℕ} {j k : ℤ}
    (hj : OscillatoryScaleSpec lam r j) (hk : OscillatoryScaleSpec lam r k) : j = k := by
  have ha : 0 ≤ Real.sqrt |lam| := Real.sqrt_nonneg _
  apply le_antisymm
  · by_contra h
    have hkj : k < j := lt_of_not_ge h
    have hstep : k + 1 ≤ j := Int.add_one_le_iff.mpr hkj
    have hpows : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hstep
    have hdouble : (2 : ℝ) ^ (r + 1) ≤
        (2 : ℝ) ^ (k + 1) * Real.sqrt |lam| := by
      rw [pow_succ, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      nlinarith [hk.1]
    have hcomp := mul_le_mul_of_nonneg_right hpows ha
    exact (not_lt_of_ge (hdouble.trans hcomp)) hj.2
  · by_contra h
    have hjk : j < k := lt_of_not_ge h
    have hstep : j + 1 ≤ k := Int.add_one_le_iff.mpr hjk
    have hpows : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hstep
    have hdouble : (2 : ℝ) ^ (r + 1) ≤
        (2 : ℝ) ^ (j + 1) * Real.sqrt |lam| := by
      rw [pow_succ, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      nlinarith [hj.1]
    have hcomp := mul_le_mul_of_nonneg_right hpows ha
    exact (not_lt_of_ge (hdouble.trans hcomp)) hk.2

/-- The dyadic scale required by the paper exists and is unique whenever the
quadratic modulation parameter is nonzero.
@isnad1 id=existsun.1h2v.s4.feb5382eda71 from=translated src=- shape=1c4501b3 vocab=2e6cf422
-/
theorem existsUnique_oscillatoryScaleSpec (lam : ℝ) (r : ℕ) (hlam : lam ≠ 0) :
    ∃! j : ℤ, OscillatoryScaleSpec lam r j := by
  have ha : 0 < Real.sqrt |lam| := Real.sqrt_pos.2 (abs_pos.mpr hlam)
  have hx : 0 < (2 : ℝ) ^ r / Real.sqrt |lam| := div_pos (by positivity) ha
  obtain ⟨n, hnlo, hnhi⟩ :=
    exists_mem_Ioc_zpow hx (by norm_num : (1 : ℝ) < 2)
  have hnSpec : OscillatoryScaleSpec lam r (n + 1) := by
    constructor
    · rw [show (2 : ℝ) ^ r =
          ((2 : ℝ) ^ r / Real.sqrt |lam|) * Real.sqrt |lam| by field_simp]
      exact mul_le_mul_of_nonneg_right hnhi ha.le
    · rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have hmul := mul_lt_mul_of_pos_right hnlo ha
      rw [div_mul_cancel₀ _ ha.ne'] at hmul
      rw [pow_succ]
      nlinarith
  exact ⟨n + 1, hnSpec, fun k hk ↦ oscillatoryScaleSpec_unique hk hnSpec⟩

/-- The paper's integer `j(lam,r)`.  The proof argument records that the
frequency is nonzero; proof irrelevance makes its value independent of how
that fact is supplied.-/
noncomputable def oscillatoryScaleIndex (lam : ℝ) (r : ℕ) (hlam : lam ≠ 0) : ℤ :=
  Classical.choose (existsUnique_oscillatoryScaleSpec lam r hlam)

/--
@isnad1 id=oscillat.1h2v.s4.7d7f0d2469b2 from=translated src=- shape=da0c5712 vocab=6c98f395
-/
theorem oscillatoryScaleIndex_spec (lam : ℝ) (r : ℕ) (hlam : lam ≠ 0) :
    OscillatoryScaleSpec lam r (oscillatoryScaleIndex lam r hlam) :=
  (Classical.choose_spec (existsUnique_oscillatoryScaleSpec lam r hlam)).1

/--
@isnad1 id=eq.2h3v.s4.a3d7c94fd0dd from=translated src=- shape=ec24f9ca vocab=264cf9d4
-/
theorem oscillatoryScaleIndex_unique (lam : ℝ) (r : ℕ) (hlam : lam ≠ 0)
    {j : ℤ} (hj : OscillatoryScaleSpec lam r j) :
    j = oscillatoryScaleIndex lam r hlam :=
  oscillatoryScaleSpec_unique hj (oscillatoryScaleIndex_spec lam r hlam)

/-- Successive oscillation heights select successive dyadic spatial scales.
@isnad1 id=eq.1h2v.s5.022401b68785 from=translated src=- shape=5d284a93 vocab=d1de87bb
-/
theorem oscillatoryScaleIndex_succ (lam : ℝ) (r : ℕ) (hlam : lam ≠ 0) :
    oscillatoryScaleIndex lam (r + 1) hlam =
      oscillatoryScaleIndex lam r hlam + 1 := by
  have h := oscillatoryScaleIndex_spec lam r hlam
  have hnext : OscillatoryScaleSpec lam (r + 1)
      (oscillatoryScaleIndex lam r hlam + 1) := by
    constructor
    · rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), pow_succ]
      nlinarith [h.1]
    · rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), pow_succ]
      nlinarith [h.2]
  exact oscillatoryScaleSpec_unique
    (oscillatoryScaleIndex_spec lam (r + 1) hlam) hnext

/-- An explicit affine description of all selected scales relative to height
zero.
@isnad1 id=eq.1h2v.s5.bfc36bd888b1 from=translated src=- shape=4e584ea4 vocab=59e99064
-/
theorem oscillatoryScaleIndex_eq_add (lam : ℝ) (r : ℕ) (hlam : lam ≠ 0) :
    oscillatoryScaleIndex lam r hlam =
      oscillatoryScaleIndex lam 0 hlam + r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [oscillatoryScaleIndex_succ, ih]
      push_cast
      ring

/-- A selected dyadic piece lives at normalized radius between fixed
constants at its oscillation height.
@isnad1 id=and.2h3v.s7.ef3e06bfee77 from=translated src=- shape=68035d4d vocab=24242010
-/
theorem dyadicPsi_oscillatoryScaleIndex_support_normalized
    {lam : ℝ} (hlam : lam ≠ 0) (r : ℕ) {t : ℝ}
    (ht : t ∈ support (dyadicPsi (oscillatoryScaleIndex lam r hlam))) :
    (2 : ℝ) ^ ((r : ℤ) - 3) < |t| * Real.sqrt |lam| ∧
      |t| * Real.sqrt |lam| < (2 : ℝ) ^ r := by
  have ha : 0 < Real.sqrt |lam| := Real.sqrt_pos.2 (abs_pos.mpr hlam)
  have hj := dyadicPsi_support_subset (oscillatoryScaleIndex lam r hlam) ht
  have hs := oscillatoryScaleIndex_spec lam r hlam
  constructor
  · have hmul := mul_lt_mul_of_pos_right hj.1 ha
    calc
      (2 : ℝ) ^ ((r : ℤ) - 3) = (2 : ℝ) ^ r / 8 := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
        norm_num
      _ ≤ ((2 : ℝ) ^ (oscillatoryScaleIndex lam r hlam) *
          Real.sqrt |lam|) / 8 := div_le_div_of_nonneg_right hs.1 (by norm_num)
      _ = (2 : ℝ) ^ (oscillatoryScaleIndex lam r hlam - 3) *
          Real.sqrt |lam| := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        ring
      _ < |t| * Real.sqrt |lam| := hmul
  · have hmul := mul_lt_mul_of_pos_right hj.2 ha
    calc
      |t| * Real.sqrt |lam| <
          (2 : ℝ) ^ (oscillatoryScaleIndex lam r hlam - 1) *
            Real.sqrt |lam| := hmul
      _ = ((2 : ℝ) ^ (oscillatoryScaleIndex lam r hlam) *
          Real.sqrt |lam|) / 2 := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        ring
      _ < (2 : ℝ) ^ (r + 1) / 2 :=
        div_lt_div_of_pos_right hs.2 (by norm_num)
      _ = (2 : ℝ) ^ r := by rw [pow_succ]; ring

/-! A finite low-oscillatory kernel.  We first keep the selector `J` explicit
so that the elementary kernel algebra can be reused, and then specialize it
to `oscillatoryScaleIndex`. -/
noncomputable def lowOscillatoryKernel (lam : ℝ) (B : ℕ) (J : ℕ → ℤ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (B + 1),
    (dyadicPsi (J r) t : ℂ) * phase (lam * t ^ 2)

/--
@isnad1 id=eq.1h4v.s6.9591aad4b309 from=translated src=- shape=99e6d8e0 vocab=c5370930
-/
theorem lowOscillatoryKernel_eq_zero_of_not_mem_supports
    (lam : ℝ) (B : ℕ) (J : ℕ → ℤ) (t : ℝ)
    (ht : ∀ r ∈ Finset.range (B + 1), t ∉ support (dyadicPsi (J r))) :
    lowOscillatoryKernel lam B J t = 0 := by
  rw [lowOscillatoryKernel]
  apply Finset.sum_eq_zero
  intro r hr
  have hψ : dyadicPsi (J r) t = 0 := by
    simpa [Function.support] using ht r hr
  simp [hψ]

/--
@isnad1 id=le.0h3v.s6.af0cd63bd334 from=translated src=- shape=8b55a262 vocab=1e6c9c07
-/
theorem lowOscillatoryKernel_support_subset (lam : ℝ) (B : ℕ) (J : ℕ → ℤ) :
    support (lowOscillatoryKernel lam B J) ⊆
      ⋃ r ∈ Finset.range (B + 1), support (dyadicPsi (J r)) := by
  intro t ht
  by_contra hnot
  apply ht
  apply lowOscillatoryKernel_eq_zero_of_not_mem_supports
  intro r hr
  by_contra hmem
  apply hnot
  exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, hmem⟩⟩

/--
@isnad1 id=le.1h2v.s5.aba99861ef77 from=translated src=- shape=3530cb55 vocab=9d231870
-/
theorem norm_dyadicPsi_le (j : ℤ) {t : ℝ} (ht : t ≠ 0) :
    |dyadicPsi j t| ≤ 2 / |t| := by
  rw [dyadicPsi_eq_quotient ht, abs_div]
  have h₁ := dyadicCutoff_nonneg (2⁻¹ ^ j * t)
  have h₂ := dyadicCutoff_le_one (2⁻¹ ^ j * t)
  have h₃ := dyadicCutoff_nonneg (2⁻¹ ^ (j - 1) * t)
  have h₄ := dyadicCutoff_le_one (2⁻¹ ^ (j - 1) * t)
  have hnum :
      |dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)| ≤ 2 := by
    calc
      |dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)| ≤
          |dyadicCutoff (2⁻¹ ^ j * t)| +
            |dyadicCutoff (2⁻¹ ^ (j - 1) * t)| := by
        simpa [sub_eq_add_neg] using
          (abs_add_le
            (dyadicCutoff (2⁻¹ ^ j * t))
            (-dyadicCutoff (2⁻¹ ^ (j - 1) * t)))
      _ = dyadicCutoff (2⁻¹ ^ j * t) +
            dyadicCutoff (2⁻¹ ^ (j - 1) * t) := by
        rw [abs_of_nonneg h₁, abs_of_nonneg h₃]
      _ ≤ 2 := by linarith
  exact (div_le_div_of_nonneg_right hnum (abs_nonneg _))

/--
@isnad1 id=le.1h4v.s6.1628fa5010da from=translated src=- shape=587aa588 vocab=a31bafd8
-/
theorem lowOscillatoryKernel_norm_le {lam : ℝ} {B : ℕ} {J : ℕ → ℤ}
    {t : ℝ} (ht : t ≠ 0) :
    ‖lowOscillatoryKernel lam B J t‖ ≤ (B + 1 : ℝ) * (2 / |t|) := by
  rw [lowOscillatoryKernel]
  calc
    ‖∑ r ∈ Finset.range (B + 1),
        (dyadicPsi (J r) t : ℂ) * phase (lam * t ^ 2)‖ ≤
        ∑ r ∈ Finset.range (B + 1),
          ‖(dyadicPsi (J r) t : ℂ) * phase (lam * t ^ 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range (B + 1), (2 / |t|) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact norm_dyadicPsi_le (J r) ht
    _ = (B + 1 : ℝ) * (2 / |t|) := by
      simp [Finset.sum_const, Nat.cast_add, Nat.cast_one]

/--
@isnad1 id=le.0h3v.s7.3c240f9bbb56 from=translated src=- shape=783c69f4 vocab=1a68275b
-/
theorem lowOscillatoryKernel_support_annulus_subset (lam : ℝ) (B : ℕ) (J : ℕ → ℤ) :
    support (lowOscillatoryKernel lam B J) ⊆
      ⋃ r ∈ Finset.range (B + 1),
        {t : ℝ | 2 ^ (J r - 3 : ℤ) < |t| ∧
          |t| < 2 ^ (J r - 1 : ℤ)} := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := Set.mem_iUnion₂.mp
    (lowOscillatoryKernel_support_subset lam B J ht)
  exact Set.mem_iUnion₂.2 ⟨r, hr, dyadicPsi_support_subset (J r) hrt⟩

/-- Consecutive dyadic pieces telescope exactly.  This is the cancellation
behind the uniform size estimate for the finite low-oscillation kernel.
@isnad1 id=eq.1h3v.s7.90469fa0d7ae from=translated src=- shape=4b09c058 vocab=3d8036fc
-/
theorem sum_dyadicPsi_consecutive (j : ℤ) (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ∑ r ∈ Finset.range n, dyadicPsi (j + (r : ℤ)) t =
      (dyadicCutoff ((2⁻¹ : ℝ) ^ (j + (n : ℤ) - 1) * t) -
        dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t)) / t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, dyadicPsi_eq_quotient ht]
      push_cast
      ring_nf

/-- The exact finite kernel `K_{λ,B}` appearing in the low-oscillation part
of the positive proof.-/
noncomputable def paperLowOscillatoryKernel
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) (t : ℝ) : ℂ :=
  lowOscillatoryKernel lam B (fun r ↦ oscillatoryScaleIndex lam r hlam) t

/-- The finite low-oscillation kernel is one telescoping cutoff difference
times the common quadratic phase.
@isnad1 id=eq.2h3v.s7.8c6c3035c428 from=translated src=- shape=73ec1fb5 vocab=123b153c
-/
theorem paperLowOscillatoryKernel_eq_cutoffDifference
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    paperLowOscillatoryKernel lam hlam B t =
      (((dyadicCutoff
          ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam + (B : ℤ)) * t) -
        dyadicCutoff
          ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)) / t : ℝ) : ℂ) *
        phase (lam * t ^ 2) := by
  rw [paperLowOscillatoryKernel, lowOscillatoryKernel]
  have hsum :
      (∑ r ∈ Finset.range (B + 1),
          (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam * t ^ 2)) =
        ∑ r ∈ Finset.range (B + 1),
          (dyadicPsi (oscillatoryScaleIndex lam 0 hlam + (r : ℤ)) t : ℂ) *
            phase (lam * t ^ 2) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [oscillatoryScaleIndex_eq_add]
  rw [hsum, ← Finset.sum_mul]
  congr 1
  norm_cast
  convert sum_dyadicPsi_consecutive
    (oscillatoryScaleIndex lam 0 hlam) (B + 1) ht using 1
  push_cast
  ring_nf

/--
@isnad1 id=le.2h3v.s6.79d5a87a5c69 from=translated src=- shape=161aa1c6 vocab=732ca7c7
-/
theorem paperLowOscillatoryKernel_norm_le
    {lam : ℝ} (hlam : lam ≠ 0) {B : ℕ} {t : ℝ} (ht : t ≠ 0) :
    ‖paperLowOscillatoryKernel lam hlam B t‖ ≤ (B + 1 : ℝ) * (2 / |t|) := by
  exact lowOscillatoryKernel_norm_le ht

/-- The sharp size estimate stated in the paper, independent of the number of
included heights.
@isnad1 id=le.2h3v.s5.dc93ab9a0a9e from=translated src=- shape=b865c9cd vocab=4b76684b
-/
theorem paperLowOscillatoryKernel_norm_le_inv_abs
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖paperLowOscillatoryKernel lam hlam B t‖ ≤ 1 / |t| := by
  rw [paperLowOscillatoryKernel_eq_cutoffDifference hlam B ht,
    norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have h₁ := dyadicCutoff_nonneg
    ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam + (B : ℤ)) * t)
  have h₂ := dyadicCutoff_le_one
    ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam + (B : ℤ)) * t)
  have h₃ := dyadicCutoff_nonneg
    ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)
  have h₄ := dyadicCutoff_le_one
    ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)
  have hnum :
      |dyadicCutoff
          ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam + (B : ℤ)) * t) -
        dyadicCutoff
          ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  exact div_le_div_of_nonneg_right hnum (abs_nonneg t)

/--
@isnad1 id=le.1h3v.s5.4a8b2908aed7 from=translated src=- shape=cd1e18d4 vocab=86555abd
-/
theorem paperLowOscillatoryKernel_mul_norm_le_one
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) (t : ℝ) :
    ‖(t : ℂ) * paperLowOscillatoryKernel lam hlam B t‖ ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |t| * ‖paperLowOscillatoryKernel lam hlam B t‖ ≤ |t| * (1 / |t|) :=
        mul_le_mul_of_nonneg_left
          (paperLowOscillatoryKernel_norm_le_inv_abs hlam B ht) (abs_nonneg t)
      _ = 1 := by field_simp

/--
@isnad1 id=le.1h2v.s7.15a85b66006c from=translated src=- shape=14db63ca vocab=405ae6cc
-/
theorem paperLowOscillatoryKernel_support_annulus_subset
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) :
    support (paperLowOscillatoryKernel lam hlam B) ⊆
      ⋃ r ∈ Finset.range (B + 1),
        {t : ℝ |
          2 ^ (oscillatoryScaleIndex lam r hlam - 3 : ℤ) < |t| ∧
          |t| < 2 ^ (oscillatoryScaleIndex lam r hlam - 1 : ℤ)} := by
  exact lowOscillatoryKernel_support_annulus_subset lam B
    (fun r ↦ oscillatoryScaleIndex lam r hlam)

/-- The normalized support observation used in the lacunary positive proof:
`K_{λ,B}` is supported where `|t|√|λ|` lies between an absolute
constant and `2^B`.
@isnad1 id=le.1h2v.s6.f75c9a1c28db from=translated src=- shape=e1f3f9e2 vocab=aca64948
-/
theorem paperLowOscillatoryKernel_support_normalized
    (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ) :
    support (paperLowOscillatoryKernel lam hlam B) ⊆
      {t : ℝ | (1 / 8 : ℝ) < |t| * Real.sqrt |lam| ∧
        |t| * Real.sqrt |lam| < (2 : ℝ) ^ B} := by
  intro t ht
  obtain ⟨r, hr, hrt⟩ := Set.mem_iUnion₂.mp
    (lowOscillatoryKernel_support_subset lam B
      (fun q ↦ oscillatoryScaleIndex lam q hlam) ht)
  have hrB : r ≤ B := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hnorm := dyadicPsi_oscillatoryScaleIndex_support_normalized hlam r hrt
  constructor
  · calc
      (1 / 8 : ℝ) = (2 : ℝ) ^ ((0 : ℤ) - 3) := by norm_num
      _ ≤ (2 : ℝ) ^ ((r : ℤ) - 3) := by
        apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2
        omega
      _ < |t| * Real.sqrt |lam| := hnorm.1
  · exact hnorm.2.trans_le (pow_le_pow_right₀ (by norm_num) hrB)

end QuadraticCarleson
