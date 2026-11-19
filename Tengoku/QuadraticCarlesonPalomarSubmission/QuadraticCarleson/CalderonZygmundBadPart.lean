/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cancellative Calderón--Zygmund bad-part estimate in one dimension

This file formalizes the one-dimensional Lipschitz-kernel specialization of
Lemma 6.12 on printed page 114 of the harmonic-analysis notes supplied by the
author.  It is the form needed for the low oscillatory part of the positive
theorem: an atom supported on an interval has mean zero, so subtracting the
kernel at the interval center converts cancellation into spatial decay.
-/

open MeasureTheory Set

namespace QuadraticCarleson

set_option autoImplicit false

/-- The one-dimensional cube of side length `R` centered at `z`, represented
half-open so disjoint interval families remain literally disjoint.-/
def centeredInterval (z R : ℝ) : Set ℝ :=
  Ico (z - R / 2) (z + R / 2)

/-- The triple of the centered interval, corresponding to `Q*` in dimension
one in Lemma 6.12.-/
def tripleCenteredInterval (z R : ℝ) : Set ℝ :=
  Icc (z - 3 * R / 2) (z + 3 * R / 2)

/--
@isnad1 id=le.1h3v.s5.f7d4de387393 from=translated src=- shape=9edc6fc3 vocab=558db291
-/
theorem abs_sub_center_le_of_mem_centeredInterval {z R y : ℝ}
    (hy : y ∈ centeredInterval z R) :
    |y - z| ≤ R / 2 := by
  simp only [centeredInterval, mem_Ico] at hy
  rw [abs_le]
  constructor <;> linarith

/--
@isnad1 id=lt.1h3v.s6.2f38bbf92982 from=translated src=- shape=895c39d1 vocab=80ddaebd
-/
theorem not_mem_tripleCenteredInterval_abs {z R x : ℝ}
    (hx : x ∉ tripleCenteredInterval z R) :
    3 * R / 2 < |x - z| := by
  simp only [tripleCenteredInterval, mem_Icc, not_and_or, not_le] at hx
  rw [abs_sub_comm, lt_abs]
  rcases hx with hx | hx
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Outside the triple interval, every point of the original interval is at
least half as far from the observation point as the center is.
@isnad1 id=le.3h4v.s6.2655189131bd from=translated src=- shape=b6476570 vocab=e0821ca6
-/
theorem half_center_distance_le_distance {z R x y : ℝ} (hR : 0 ≤ R)
    (hx : x ∉ tripleCenteredInterval z R) (hy : y ∈ centeredInterval z R) :
    |x - z| / 2 ≤ |x - y| := by
  have hyz : |y - z| ≤ R / 2 := abs_sub_center_le_of_mem_centeredInterval hy
  have hxz : 3 * R / 2 < |x - z| := not_mem_tripleCenteredInterval_abs hx
  have htri : |x - z| ≤ |x - y| + |y - z| := by
    calc
      |x - z| = |(x - y) + (y - z)| := by ring_nf
      _ ≤ |x - y| + |y - z| := abs_add_le _ _
  linarith

/-- Mean-zero cancellation allows subtraction of the kernel at the interval
center.  All integrability assumptions are explicit.
@isnad1 id=eq.3h5v.s7.dd10481ddfd7 from=translated src=- shape=cfc99b7e vocab=12d77d98
-/
theorem setIntegral_kernel_eq_sub_center
    (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x z R : ℝ)
    (hf : IntegrableOn f (centeredInterval z R))
    (hKf : IntegrableOn (fun y ↦ K x y * f y) (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0) :
    (∫ y in centeredInterval z R, K x y * f y) =
      ∫ y in centeredInterval z R, (K x y - K x z) * f y := by
  have hconst : IntegrableOn (fun y ↦ K x z * f y) (centeredInterval z R) :=
    hf.const_mul (K x z)
  have hsub : IntegrableOn
      (fun y ↦ K x y * f y - K x z * f y) (centeredInterval z R) :=
    hKf.sub hconst
  calc
    (∫ y in centeredInterval z R, K x y * f y) =
        (∫ y in centeredInterval z R, K x y * f y) -
          K x z * (∫ y in centeredInterval z R, f y) := by rw [hmean, mul_zero, sub_zero]
    _ = (∫ y in centeredInterval z R, K x y * f y) -
          (∫ y in centeredInterval z R, K x z * f y) := by
            rw [integral_const_mul]
    _ = ∫ y in centeredInterval z R,
          (K x y * f y - K x z * f y) := by
            rw [integral_sub hKf hconst]
    _ = ∫ y in centeredInterval z R, (K x y - K x z) * f y := by
      apply integral_congr_ae
      filter_upwards with y
      ring

/-- A variable pointwise majorant bounds the norm of the cancelled integral.
This is the Bochner-integral step used in Lemma 6.12.
@isnad1 id=le.2h6v.s7.346bf0681251 from=translated src=- shape=d804627b vocab=6e5e105b
-/
theorem norm_setIntegral_kernel_sub_center_le
    (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x z R D : ℝ)
    (hf : IntegrableOn f (centeredInterval z R))
    (hbound : ∀ y ∈ centeredInterval z R,
      ‖(K x y - K x z) * f y‖ ≤ D * ‖f y‖) :
    ‖∫ y in centeredInterval z R, (K x y - K x z) * f y‖ ≤
      D * ∫ y in centeredInterval z R, ‖f y‖ := by
  have hmajorant : IntegrableOn (fun y ↦ D * ‖f y‖) (centeredInterval z R) :=
    hf.norm.const_mul D
  have h := norm_integral_le_of_norm_le
    (μ := volume.restrict (centeredInterval z R))
    (f := fun y ↦ (K x y - K x z) * f y)
    (g := fun y ↦ D * ‖f y‖) hmajorant (by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
      exact hbound y hy)
  simpa only [integral_const_mul] using h

/-- The exact pointwise bad-part estimate obtained from a Lipschitz
Calderón--Zygmund kernel.  The constant is explicit and uniform.
@isnad1 id=le.5h6v.s8.8629fb7d902f from=translated src=- shape=26350766 vocab=5bb6833a
-/
theorem norm_setIntegral_kernel_sub_center_le_decay
    (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x z R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C)
    (hx : x ∉ tripleCenteredInterval z R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hregular : ∀ y ∈ centeredInterval z R,
      ‖K x y - K x z‖ ≤ C * |y - z| / |x - y| ^ 2) :
    ‖∫ y in centeredInterval z R, (K x y - K x z) * f y‖ ≤
      (2 * C * R / |x - z| ^ 2) *
        ∫ y in centeredInterval z R, ‖f y‖ := by
  apply norm_setIntegral_kernel_sub_center_le K f x z R
    (2 * C * R / |x - z| ^ 2) hf
  intro y hy
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (f y))
  calc
    ‖K x y - K x z‖ ≤ C * |y - z| / |x - y| ^ 2 := hregular y hy
    _ ≤ C * (R / 2) / (|x - z| / 2) ^ 2 := by
      have hyz := abs_sub_center_le_of_mem_centeredInterval hy
      have hdist := half_center_distance_le_distance hR.le hx hy
      have hxz : 0 < |x - z| := by
        have := not_mem_tripleCenteredInterval_abs hx
        linarith
      gcongr
    _ = 2 * C * R / |x - z| ^ 2 := by ring

/-- The pointwise conclusion of Lemma 6.12 in the one-dimensional,
Lipschitz-kernel form used in the paper.
@isnad1 id=le.7h6v.s8.29949743ace7 from=translated src=- shape=b3452f4c vocab=5bb6833a
-/
theorem norm_setIntegral_kernel_le_decay
    (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (x z R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C)
    (hx : x ∉ tripleCenteredInterval z R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hKf : IntegrableOn (fun y ↦ K x y * f y) (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0)
    (hregular : ∀ y ∈ centeredInterval z R,
      ‖K x y - K x z‖ ≤ C * |y - z| / |x - y| ^ 2) :
    ‖∫ y in centeredInterval z R, K x y * f y‖ ≤
      (2 * C * R / |x - z| ^ 2) *
        ∫ y in centeredInterval z R, ‖f y‖ := by
  rw [setIntegral_kernel_eq_sub_center K f x z R hf hKf hmean]
  exact norm_setIntegral_kernel_sub_center_le_decay K f x z R C
    hR hC hx hf hregular

/-! ## Exact integration of the one-dimensional decay majorant -/

/-- The inverse-square majorant is integrable on the right tail.
@isnad1 id=integrab.1h2v.s6.86e3eea29473 from=translated src=- shape=8ff1fce7 vocab=6eb39977
-/
theorem integrableOn_inv_abs_sub_sq_Ioi (z d : ℝ) (hd : 0 < d) :
    IntegrableOn (fun x : ℝ ↦ 1 / |x - z| ^ 2) (Ioi (z + d)) := by
  have hp : IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Ioi d) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hd
  have hpres := measurePreserving_add_right (volume : Measure ℝ) z
  have hemb := (MeasurableEquiv.addRight z).measurableEmbedding
  rw [← hpres.integrableOn_comp_preimage hemb]
  have hset : (fun x : ℝ ↦ x + z) ⁻¹' Ioi (z + d) = Ioi d := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine hp.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hd.trans hx
  simp only [Function.comp_apply, add_sub_cancel_right, abs_of_pos hx0]
  rw [Real.rpow_neg hx0.le, Real.rpow_two, one_div]

/-- The exact integral of the inverse-square majorant on the right tail.
@isnad1 id=eq.1h2v.s6.0647c2d1a8ab from=translated src=- shape=4c618f54 vocab=ec4572e1
-/
theorem integral_inv_abs_sub_sq_Ioi (z d : ℝ) (hd : 0 < d) :
    ∫ x in Ioi (z + d), 1 / |x - z| ^ 2 = 1 / d := by
  rw [← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self
    ((Ioi (z + d)).indicator (fun x : ℝ ↦ 1 / |x - z| ^ 2)) z]
  have hind : (fun x : ℝ ↦ (Ioi (z + d)).indicator
      (fun u : ℝ ↦ 1 / |u - z| ^ 2) (x + z)) =
      (Ioi d).indicator (fun x : ℝ ↦ x ^ (-2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Ioi d
    · have hx0 : 0 < x := hd.trans hx
      rw [indicator_of_mem hx]
      have hx' : x + z ∈ Ioi (z + d) := by
        rw [mem_Ioi] at hx ⊢
        linarith
      rw [indicator_of_mem hx']
      have habs : |x + z - z| = x := by
        rw [add_sub_cancel_right, abs_of_pos hx0]
      rw [habs, Real.rpow_neg hx0.le, Real.rpow_two, one_div]
    · rw [indicator_of_notMem hx]
      have hx' : x + z ∉ Ioi (z + d) := by
        rw [mem_Ioi, not_lt] at hx ⊢
        linarith
      rw [indicator_of_notMem hx']
  rw [hind, integral_indicator measurableSet_Ioi,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- The inverse-square majorant is integrable on the reflected left tail.
@isnad1 id=integrab.1h2v.s6.aa46250f7acf from=translated src=- shape=edc1cdf1 vocab=069b4161
-/
theorem integrableOn_inv_abs_sub_sq_Iio (z d : ℝ) (hd : 0 < d) :
    IntegrableOn (fun x : ℝ ↦ 1 / |x - z| ^ 2) (Iio (z - d)) := by
  have hr := integrableOn_inv_abs_sub_sq_Ioi (-z) d hd
  have hpres := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hemb := (MeasurableEquiv.neg ℝ).measurableEmbedding
  rw [← hpres.integrableOn_comp_preimage hemb]
  have hset : (fun x : ℝ ↦ -x) ⁻¹' Iio (z - d) = Ioi (-z + d) := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine hr.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [Function.comp_apply]
  have heq : -x - z = -(x - -z) := by ring
  rw [heq, abs_neg]

/-- The exact integral of the inverse-square majorant on the left tail.
@isnad1 id=eq.1h2v.s6.0e3e70e557d1 from=translated src=- shape=0b4d990b vocab=d0aab1dc
-/
theorem integral_inv_abs_sub_sq_Iio (z d : ℝ) (hd : 0 < d) :
    ∫ x in Iio (z - d), 1 / |x - z| ^ 2 = 1 / d := by
  rw [← integral_Iic_eq_integral_Iio]
  have hc : z - d = -(-z + d) := by ring
  rw [hc, ← integral_comp_neg_Ioi]
  calc
    (∫ x in Ioi (-z + d), 1 / |-x - z| ^ 2) =
        ∫ x in Ioi (-z + d), 1 / |x - (-z)| ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 1 / |-x - z| ^ 2 = 1 / |x - -z| ^ 2
      have heq : -x - z = -(x - -z) := by ring
      rw [heq, abs_neg]
    _ = 1 / d := integral_inv_abs_sub_sq_Ioi (-z) d hd

/-- The complement of the triple interval is the disjoint union of its two
open tails.
@isnad1 id=eq.0h2v.s6.85acf0559ddd from=translated src=- shape=56d3134b vocab=c3476e8f
-/
theorem compl_tripleCenteredInterval (z R : ℝ) :
    (tripleCenteredInterval z R)ᶜ =
      Iio (z - 3 * R / 2) ∪ Ioi (z + 3 * R / 2) := by
  ext x
  simp only [tripleCenteredInterval, mem_compl_iff, mem_Icc, mem_union,
    mem_Iio, mem_Ioi, not_and_or, not_le]

/-- The decay majorant is integrable off the triple interval.
@isnad1 id=integrab.1h2v.s6.9dd00a352ba0 from=translated src=- shape=5f23e2ab vocab=a6d4805b
-/
theorem integrableOn_inv_abs_sub_sq_compl_tripleCenteredInterval
    (z R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : ℝ ↦ 1 / |x - z| ^ 2)
      (tripleCenteredInterval z R)ᶜ := by
  have hd : 0 < 3 * R / 2 := by positivity
  rw [compl_tripleCenteredInterval]
  exact (integrableOn_inv_abs_sub_sq_Iio z (3 * R / 2) hd).union
    (integrableOn_inv_abs_sub_sq_Ioi z (3 * R / 2) hd)

/-- In dimension one the inverse-square tail outside the triple interval has
the exact mass `4 / (3R)`.
@isnad1 id=eq.1h2v.s7.f4ef866ad57a from=translated src=- shape=7342f04f vocab=6f1ea999
-/
theorem integral_inv_abs_sub_sq_compl_tripleCenteredInterval
    (z R : ℝ) (hR : 0 < R) :
    ∫ x in (tripleCenteredInterval z R)ᶜ, 1 / |x - z| ^ 2 = 4 / (3 * R) := by
  have hd : 0 < 3 * R / 2 := by positivity
  have hdis : Disjoint (Iio (z - 3 * R / 2)) (Ioi (z + 3 * R / 2)) := by
    rw [Set.disjoint_left]
    intro x hxl hxr
    simp only [mem_Iio] at hxl
    simp only [mem_Ioi] at hxr
    linarith
  have hl := integrableOn_inv_abs_sub_sq_Iio z (3 * R / 2) hd
  have hr := integrableOn_inv_abs_sub_sq_Ioi z (3 * R / 2) hd
  rw [compl_tripleCenteredInterval,
    setIntegral_union hdis measurableSet_Ioi hl hr]
  rw [show z - 3 * R / 2 = z - (3 * R / 2) by ring,
    integral_inv_abs_sub_sq_Iio z (3 * R / 2) hd,
    integral_inv_abs_sub_sq_Ioi z (3 * R / 2) hd]
  field_simp
  ring

/-! ## Integrated bad-part estimate -/

/-- The integrated conclusion of Lemma 6.12 in the one-dimensional
Lipschitz-kernel form used by the paper.  Measurability of the kernel output is
kept explicit; in applications it follows from the measurable operator
realization.  The proof gives the uniform constant `8C/3`.
@isnad1 id=le.7h5v.s9.e6dfc419882e from=translated src=- shape=69737c43 vocab=45592b7e
-/
theorem integral_norm_setIntegral_kernel_le
    (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (z R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : IntegrableOn f (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0)
    (hKf : ∀ x ∉ tripleCenteredInterval z R,
      IntegrableOn (fun y ↦ K x y * f y) (centeredInterval z R))
    (hregular : ∀ x ∉ tripleCenteredInterval z R,
      ∀ y ∈ centeredInterval z R,
        ‖K x y - K x z‖ ≤ C * |y - z| / |x - y| ^ 2)
    (hmeas : AEStronglyMeasurable
      (fun x ↦ ∫ y in centeredInterval z R, K x y * f y)
      (volume.restrict (tripleCenteredInterval z R)ᶜ)) :
    ∫ x in (tripleCenteredInterval z R)ᶜ,
        ‖∫ y in centeredInterval z R, K x y * f y‖ ≤
      (8 * C / 3) * ∫ y in centeredInterval z R, ‖f y‖ := by
  let A : ℝ := ∫ y in centeredInterval z R, ‖f y‖
  have hcompl : MeasurableSet (tripleCenteredInterval z R)ᶜ := by
    simpa only [tripleCenteredInterval] using
      (measurableSet_Icc.compl : MeasurableSet
        (Icc (z - 3 * R / 2) (z + 3 * R / 2))ᶜ)
  have hinv := integrableOn_inv_abs_sub_sq_compl_tripleCenteredInterval z R hR
  have hmaj : IntegrableOn
      (fun x : ℝ ↦ (2 * C * R * A) * (1 / |x - z| ^ 2))
      (tripleCenteredInterval z R)ᶜ := hinv.const_mul (2 * C * R * A)
  have hpoint : ∀ x ∉ tripleCenteredInterval z R,
      ‖∫ y in centeredInterval z R, K x y * f y‖ ≤
        (2 * C * R * A) * (1 / |x - z| ^ 2) := by
    intro x hx
    calc
      ‖∫ y in centeredInterval z R, K x y * f y‖ ≤
          (2 * C * R / |x - z| ^ 2) *
            ∫ y in centeredInterval z R, ‖f y‖ :=
        norm_setIntegral_kernel_le_decay K f x z R C hR hC hx hf (hKf x hx)
          hmean (hregular x hx)
      _ = (2 * C * R * A) * (1 / |x - z| ^ 2) := by
        simp only [A]
        ring
  have htarget : IntegrableOn
      (fun x ↦ ‖∫ y in centeredInterval z R, K x y * f y‖)
      (tripleCenteredInterval z R)ᶜ := by
    apply hmaj.mono' hmeas.norm
    filter_upwards [ae_restrict_mem hcompl] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hpoint x hx
  calc
    (∫ x in (tripleCenteredInterval z R)ᶜ,
        ‖∫ y in centeredInterval z R, K x y * f y‖) ≤
        ∫ x in (tripleCenteredInterval z R)ᶜ,
          (2 * C * R * A) * (1 / |x - z| ^ 2) := by
      apply integral_mono_ae htarget hmaj
      filter_upwards [ae_restrict_mem hcompl] with x hx
      exact hpoint x hx
    _ = (2 * C * R * A) * (4 / (3 * R)) := by
      rw [integral_const_mul,
        integral_inv_abs_sub_sq_compl_tripleCenteredInterval z R hR]
    _ = (8 * C / 3) * ∫ y in centeredInterval z R, ‖f y‖ := by
      simp only [A]
      field_simp
      ring

end QuadraticCarleson
