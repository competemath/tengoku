/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# Integration and averages on parabolic cylinders

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module records generic average identities and
the product-measure formulas used on balls and parabolic cylinders.

The source-facing scale-invariant quantities are intentionally not defined
here.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

private theorem continuous_vec3EuclideanNorm_sub (x : Vec3) :
    Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
  unfold vec3EuclideanNorm
  fun_prop

private theorem norm_vec3_sub_le_euclideanNorm (x y : Vec3) :
    ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |(y - x) i| ≤ vec3EuclideanNorm (y - x)
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg ((y - x) j)) (Finset.mem_univ i)

/-! ### Measures and cylinder Fubini -/

/-- The volume measure on `ParabolicPoint` is the product of spatial and time volume.
@isnad1 id=eq.0h0v.s6.3bf42e6dd100 from=translated src=- shape=b6ff55a2 vocab=42c2779d
-/
theorem volume_parabolicPoint_eq_prod :
    (volume : Measure ParabolicPoint) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) :=
  rfl

/-- A positive-radius Euclidean spatial ball has positive volume.
@isnad1 id=lt.1h2v.s7.25738505ee77 from=translated src=- shape=1f6f2e9a vocab=16c26544
-/
theorem volume_vec3Ball_pos {x : Vec3} {r : ℝ} (hr : 0 < r) :
    0 < volume (vec3Ball x r) := by
  have hopen : IsOpen (vec3Ball x r) := by
    unfold vec3Ball
    exact isOpen_lt (continuous_vec3EuclideanNorm_sub x) continuous_const
  exact hopen.measure_pos volume ⟨x, by simp [vec3EuclideanNorm_zero, hr]⟩

/-- A Euclidean spatial ball has finite volume.
@isnad1 id=lt.0h2v.s6.360fd676f753 from=translated src=- shape=561b125e vocab=1dbfe3f9
-/
theorem volume_vec3Ball_lt_top {x : Vec3} {r : ℝ} :
    volume (vec3Ball x r) < ∞ := by
  have hsub : vec3Ball x r ⊆ Metric.ball x r := by
    intro y hy
    change ‖y - x‖ < r
    exact lt_of_le_of_lt (norm_vec3_sub_le_euclideanNorm x y)
      (by
        change vec3EuclideanNorm (y - x) < r at hy
        exact hy)
  exact (measure_mono hsub).trans_lt
    (measure_ball_lt_top (μ := volume) (x := x) (r := r))

/-- A positive-radius parabolic cylinder has positive volume.
@isnad1 id=lt.1h3v.s5.5741daa60f90 from=translated src=- shape=07db46c2 vocab=d539879e
-/
theorem volume_parabolicCylinder_pos {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    0 < volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_pos (ne_of_gt (volume_vec3Ball_pos hr))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)))

/-- A parabolic cylinder has finite volume.
@isnad1 id=lt.0h3v.s5.867ea696ef87 from=translated src=- shape=32a9db26 vocab=3315deb1
-/
theorem volume_parabolicCylinder_lt_top {x : Vec3} {t r : ℝ} :
    volume (parabolicCylinder x t r) < ∞ := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_lt_top
    (volume_vec3Ball_lt_top (x := x) (r := r))
    ENNReal.ofReal_lt_top

/-- Fubini's theorem on a parabolic cylinder for Bochner-integrable functions.
@isnad1 id=eq.1h4v.s8.1ed3420fc8fd from=translated src=- shape=ea201605 vocab=bf9b1d1e
-/
theorem integral_parabolicCylinder {x : Vec3} {t r : ℝ}
    {g : ParabolicPoint → ℝ}
    (hg : IntegrableOn g (parabolicCylinder x t r) volume) :
    ∫ z in parabolicCylinder x t r, g z ∂volume =
      ∫ s in Ioc (t - r ^ 2) t, ∫ y in vec3Ball x r, g (y, s) := by
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change
    ∫ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) = _
  change IntegrableOn g (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) at hg
  have hgs :
      IntegrableOn (fun z : ℝ × Vec3 => g z.swap)
        (Ioc (t - r ^ 2) t ×ˢ vec3Ball x r)
        ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    exact hg.swap
  calc
    ∫ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) =
        ∫ z in Ioc (t - r ^ 2) t ×ˢ vec3Ball x r, g z.swap ∂
          (volume : Measure ℝ).prod (volume : Measure Vec3) :=
      (setIntegral_prod_swap (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) (vec3Ball x r) (Ioc (t - r ^ 2) t) g).symm
    _ = ∫ s in Ioc (t - r ^ 2) t, ∫ y in vec3Ball x r, g (y, s) := by
      rw [setIntegral_prod _ hgs]
      rfl

/-- Tonelli's theorem on a parabolic cylinder for nonnegative extended-real functions.
@isnad1 id=eq.1h4v.s7.5d9c3f35a62d from=translated src=- shape=b6332816 vocab=4e6053aa
-/
theorem lintegral_parabolicCylinder {x : Vec3} {t r : ℝ}
    {g : ParabolicPoint → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (parabolicCylinder x t r))) :
    ∫⁻ z in parabolicCylinder x t r, g z ∂volume =
      ∫⁻ s in Ioc (t - r ^ 2) t, ∫⁻ y in vec3Ball x r, g (y, s) := by
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change
    ∫⁻ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) = _
  exact setLIntegral_prod_symm g hg

/-! ### Generic averages -/

/-- The set average is the integral against the reciprocal real measure.
@isnad1 id=eq.0h5v.s7.dda15c965519 from=translated src=- shape=874c528e vocab=2abaf814
-/
theorem setAverage_eq_toReal_inv_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure α) (s : Set α) (f : α → E) :
    ⨍ x in s, f x ∂μ = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by
  simpa [MeasureTheory.measureReal_def] using
    (MeasureTheory.setAverage_eq μ f s)

/-- Set averages are additive when both summands are integrable.
@isnad1 id=eq.2h5v.s7.78691ac1a3fc from=translated src=- shape=c1e02886 vocab=e810f781
-/
theorem setAverage_add_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, (f + g) x ∂μ =
      ⨍ x in s, f x ∂μ + ⨍ x in s, g x ∂μ :=
  MeasureTheory.setAverage_add hf hg

/-- Set averages commute with subtraction under integrability.
@isnad1 id=eq.2h5v.s7.a9ab6a36ebbb from=translated src=- shape=c1e02886 vocab=d7d3ffb7
-/
theorem setAverage_sub_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, (f - g) x ∂μ =
      ⨍ x in s, f x ∂μ - ⨍ x in s, g x ∂μ :=
  MeasureTheory.setAverage_sub hf hg

/-- The average of a constant on a positive finite-measure set is that constant.
@isnad1 id=eq.2h4v.s6.fcd2de0a10c7 from=translated src=- shape=e18984b3 vocab=01c89c83
-/
theorem setAverage_const_of_pos_of_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} (hsPos : 0 < μ s) (hsTop : μ s < ∞) (c : ℝ) :
    ⨍ _x in s, c ∂μ = c := by
  exact MeasureTheory.setAverage_const hsPos.ne' hsTop.ne c

/-- Set averages preserve nonnegativity almost everywhere.
@isnad1 id=le.1h4v.s6.dc54678dfbb8 from=translated src=- shape=a0a00a69 vocab=67110500
-/
theorem setAverage_nonneg_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) :
    0 ≤ ⨍ x in s, f x ∂μ :=
  MeasureTheory.average_nonneg_of_ae hf

/-- The norm of an average is bounded by the average of the norm.
@isnad1 id=le.0h5v.s6.efb94763978f from=translated src=- shape=94e89ca7 vocab=88b3992f
-/
theorem setAverage_norm_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (f : α → E) :
    ‖⨍ x in s, f x ∂μ‖ ≤ ⨍ x in s, ‖f x‖ ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.norm_integral_le_integral_norm
      (μ := μ.restrict s) f)
    (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)

/-- Set averages are monotone almost everywhere.
@isnad1 id=le.3h5v.s7.e2523ee13374 from=translated src=- shape=203933ab vocab=b7e4f34f
-/
theorem setAverage_mono_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : f ≤ᵐ[μ.restrict s] g) :
    ⨍ x in s, f x ∂μ ≤ ⨍ x in s, g x ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  exact smul_le_smul_of_nonneg_left
    (MeasureTheory.setIntegral_mono_ae_restrict hf hg hfg)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

end CKN.Foundation.Parabolic.Integration
