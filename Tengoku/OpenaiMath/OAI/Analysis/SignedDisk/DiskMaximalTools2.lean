import Tengoku.OpenaiMath.OAI.Analysis.SignedDisk.ActualMarkTrees2

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DiskMaximalTools

end DiskMaximalTools

namespace PlanePotential
open LocalCancellation

end PlanePotential

namespace DiskMoments
open DiskMaximalTools

lemma signedAverage_sub_const {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage (fun y => g y-c) x t = signedAverage g x t-c := by
  have hi : IntegrableOn g (Metric.ball x t) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x t)).mono_set Metric.ball_subset_closedBall
  have hc : IntegrableOn (fun _ : ℂ => c) (Metric.ball x t) := integrableOn_const measure_ball_lt_top.ne
  unfold signedAverage
  rw [integral_sub hi hc,integral_const]
  have hv : (volume (Metric.ball x t)).toReal = Real.pi*t^2 := by
    rw [volume_disk_real x ht.le,ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real,Measure.restrict_apply_univ,hv,smul_eq_mul]
  field_simp

/-- A true disk average of a continuous function is controlled by the local
absolute-density maximal function. No maximizing-radius selection is used. -/
lemma local_average_le {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ)
    {x : ℂ} (hx : ‖x‖ ≤ 2) {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 4) :
    ENNReal.ofReal |signedAverage g x t-c| ≤
      rationalMaximal (volume.withDensity (fun y => ENNReal.ofReal
        (({y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)) y))) x := by
  let f : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ 8}.indicator (fun y => |g y-c|)
  have hf : Measurable f := ((hg.measurable.sub measurable_const).abs).indicator
    (measurableSet_le measurable_norm measurable_const)
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_le measurable_norm measurable_const)
    apply ContinuousOn.integrableOn_compact
      (show IsCompact {y : ℂ | ‖y‖ ≤ 8} by simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8)
    exact (hg.sub continuous_const).abs.continuousOn
  have hsub (y : ℂ) (hy : y ∈ Metric.ball x t) : ‖y‖ ≤ 8 := by
    have hy' : ‖y-x‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := norm_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have he : (∫ y in Metric.ball x t, f y) = ∫ y in Metric.ball x t, |g y-c| := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [f,hsub y hy]
  have hav : |signedAverage g x t-c| ≤ (∫ y in Metric.ball x t, f y)/(Real.pi*t^2) := by
    rw [← signedAverage_sub_const hg c x ht,signedAverage,abs_div,abs_of_pos (by positivity : 0 < Real.pi*t^2),he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y-c) (μ := volume.restrict (Metric.ball x t))
  have hν : (volume.withDensity (fun y => ENNReal.ofReal (f y))) (Metric.ball x t) =
      ENNReal.ofReal (∫ y in Metric.ball x t, f y) := by
    rw [withDensity_apply _ measurableSet_ball]
    exact (ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (ae_of_all _ (fun y => by dsimp [f]; exact Set.indicator_nonneg (fun _ _ => abs_nonneg _ ) y))).symm
  apply (ENNReal.ofReal_le_ofReal hav).trans
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi*t^2),← hν,← volume_disk_real x ht.le]
  exact disk_average_le_rationalMaximal_exact _ x ht
end DiskMoments

namespace PlanePotential
open LocalCancellation DiskMaximalTools DiskMoments

end PlanePotential

namespace AffineDensities
lemma fderiv_affine_bound {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ)
    {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) :
    ∃ B : ℝ, ∀ X, ‖fderiv ℝ (fun Y => g (p+r • Y)) X‖ ≤ B := by
  refine ⟨D*|r|,?_⟩
  intro X
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y)
      (r • ContinuousLinearMap.id ℝ ℂ) X := by
    simpa using ((hasFDerivAt_id X).const_smul r).const_add p
  have hd := (hg (p+r • X)).hasFDerivAt.comp X hA
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_id, mul_one]
  exact mul_le_mul_of_nonneg_right (hD _) (abs_nonneg _)
end AffineDensities

namespace CommonPrices
open DyadicHats ConeCoordinates LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

end CommonPrices

namespace PhysicalCells
open MeasureTheory Set

def unitCell : Set ℂ := {X | X.re ∈ Ico (0:ℝ) 1 ∧ X.im ∈ Ico (0:ℝ) 1}
def toUnit (p : ℂ) (r : ℝ) (y : ℂ) : ℂ := r⁻¹ • (y-p)
def cell (p : ℂ) (r : ℝ) : Set ℂ := toUnit p r ⁻¹' unitCell

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
lemma volume_unitCell : volume unitCell = 1 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  change volume unitCell = _ at he
  rw [he]
  change (volume.prod volume) (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num
lemma norm_unitCell {X : ℂ} (hX : X ∈ unitCell) : ‖X‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im X
  rw [abs_of_nonneg hX.1.1,abs_of_nonneg hX.2.1] at h
  linarith [hX.1.2,hX.2.2]
lemma toUnit_affine (p : ℂ) {r : ℝ} (hr : r ≠ 0) (X : ℂ) : toUnit p r (p+r • X) = X := by
  simp [toUnit,hr]
lemma affine_toUnit (p : ℂ) {r : ℝ} (hr : r ≠ 0) (y : ℂ) : p+r • toUnit p r y = y := by
  simp [toUnit,hr]

lemma lintegral_smul (F : ℂ → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ X : ℂ, F (r • X)) = ENNReal.ofReal ((r^2)⁻¹)*(∫⁻ y, F y) := by
  have he := (lintegral_map_equiv (μ := volume) F
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv).symm
  change (∫⁻ X : ℂ, F (r • X)) = ∫⁻ y, F y ∂Measure.map (fun X : ℂ => r • X) volume at he
  rw [he,Measure.map_addHaar_smul volume hr,lintegral_smul_measure]
  simp only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),smul_eq_mul]

lemma lintegral_toUnit (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y : ℂ, F (toUnit p r y)) = ENNReal.ofReal (r^2)*(∫⁻ X, F X) := by
  calc
    (∫⁻ y : ℂ, F (r⁻¹ • (y-p))) = ∫⁻ y : ℂ, F (r⁻¹ • y) :=
      lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun y : ℂ => F (r⁻¹ • y)) p
    _ = _ := by rw [lintegral_smul _ (inv_ne_zero hr),inv_pow,inv_inv]

/-- Exact physical-space change of variables, with the two-dimensional volume
factor and no integrability or measurability assumptions on the majorant. -/
lemma lintegral_cell (F : ℂ → ℝ≥0∞) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F y) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F (p+r • X) := by
  rw [← lintegral_indicator (cell_measurable p r),← lintegral_indicator unitCell_measurable]
  have he (y : ℂ) : (cell p r).indicator F y =
      unitCell.indicator (fun X => F (p+r • X)) (toUnit p r y) := by
    by_cases hy : y ∈ cell p r
    · rw [Set.indicator_of_mem hy,Set.indicator_of_mem (show toUnit p r y ∈ unitCell from hy),affine_toUnit p hr]
    · rw [Set.indicator_of_notMem hy,Set.indicator_of_notMem (show toUnit p r y ∉ unitCell from hy)]
  simp_rw [he]
  exact lintegral_toUnit _ p hr

lemma cell_majorant {F : ℂ → ℝ≥0∞} (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ y in cell p r, F (toUnit p r y)) = ENNReal.ofReal (r^2)*∫⁻ X in unitCell, F X := by
  rw [lintegral_cell _ p hr]
  simp only [toUnit_affine p hr]
end PhysicalCells

namespace DiskMoments
lemma signedAverage_affine (g : ℂ → ℝ) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    signedAverage (fun Y => g (p+r • Y)) X t = signedAverage g (p+r • X) (r*t) := by
  rw [signedAverage_fixedDomain _ _ ht,signedAverage_fixedDomain _ _ (mul_pos hr ht)]
  congr 1
  apply setIntegral_congr_fun measurableSet_ball
  intro Z _
  change g (p+r • (X+t • Z)) = g (p+r • X+(r*t) • Z)
  congr 1
  rw [smul_add,smul_smul]
  abel

lemma gradient_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    gradient (fun y => signedAverage g y t) x =
      (Real.pi*t^2)⁻¹ • ∫ y in Metric.ball x t, gradient g y := by
  have hi : IntegrableOn (fun z : ℂ => fderiv ℝ g (x+t • z)) (Metric.ball 0 1) :=
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0:ℂ) 1)).mono_set Metric.ball_subset_closedBall
  rw [gradient,(hasFDerivAt_signedAverage hg hD x ht).fderiv,map_smul]
  have he := (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearMap.integral_comp_comm hi
  change (∫ z in Metric.ball (0:ℂ) 1, (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ g (x+t • z))) =
    (InnerProductSpace.toDual ℝ ℂ).symm (∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ g (x+t • z)) at he
  rw [← he]
  change (1/Real.pi) • (∫ z in Metric.ball (0:ℂ) 1, gradient g (x+t • z)) = _
  rw [integral_scale_ball (fun z => gradient g (x+z)) ht,integral_translate_ball,smul_smul]
  congr 1
  ring

lemma gradient_average_affine {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (p X : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    gradient (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) X =
      r • gradient (fun y => signedAverage g y (r*t)) (p+r • X) := by
  have he : (fun Y => signedAverage (fun Z => g (p+r • Z)) Y t) =
      (fun Y => signedAverage g (p+r • Y) (r*t)) := by
    funext Y
    exact signedAverage_affine g p Y hr ht
  rw [he]
  exact AffineDensities.gradient_affine (fun y =>
    (hasFDerivAt_signedAverage hg hD y (mul_pos hr ht)).differentiableAt) p r X

def PhysicalNeighborhoodRadius (g : ℂ → ℝ) (r : ℝ) (x : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc r (2*r) ∧ ∀ s, 0 < s → |s-t| ≤ r/4 → signedAverage g x s ≤ signedAverage g x t

def PhysicalEndpointRadius (g : ℂ → ℝ) (r : ℝ) (x : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc r (2*r) ∧ (t = r ∨ t = 2*r ∨ ∀ s ∈ Icc r (2*r), signedAverage g x s ≤ signedAverage g x t)

lemma neighborhoodRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalNeighborhoodRadius g r (p+r • X) (r*t)) :
    NeighborhoodRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  intro s hs habs
  rw [signedAverage_affine _ _ _ hr hs,signedAverage_affine _ _ _ hr (by linarith)]
  apply ht.2 (r*s) (mul_pos hr hs)
  rw [← mul_sub,abs_mul,abs_of_pos hr]
  nlinarith

lemma endpointRadius_affine {g : ℂ → ℝ} (p X : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : PhysicalEndpointRadius g r (p+r • X) (r*t)) :
    EndpointRadius (fun Y => g (p+r • Y)) X t := by
  have ht1 : 1 ≤ t := (le_of_mul_le_mul_left (by simpa only [mul_one] using ht.1.1) hr)
  have ht2 : t ≤ 2 := (le_of_mul_le_mul_left (by simpa only [mul_comm 2 r] using ht.1.2) hr)
  refine ⟨⟨ht1,ht2⟩,?_⟩
  rcases ht.2 with he | he | he
  · left
    nlinarith
  · right; left
    nlinarith
  · right; right
    intro s hs
    rw [signedAverage_affine _ _ _ hr (by linarith [hs.1]),signedAverage_affine _ _ _ hr (by linarith)]
    exact he (r*s) ⟨by nlinarith [hs.1],by nlinarith [hs.2]⟩
end DiskMoments

end SignedDisk

end

end OAI
