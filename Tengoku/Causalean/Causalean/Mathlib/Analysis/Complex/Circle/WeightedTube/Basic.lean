module
public import Tengoku

/-!
# Geometry and weights for a circular tube

This module supplies a neutral Euclidean-plane model of the unit circle, its inward and outward
sides, and the radial power weight used for local volume calculations. The plane is represented by
complex numbers, which carry the standard two-dimensional Euclidean metric and Lebesgue measure.
-/

@[expose] public section

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal NNReal Real Topology

namespace Causalean.Mathlib.Analysis.Complex.Circle.WeightedTube

/-- The [Euclidean plane](goal) is represented by the complex numbers, equipped with their standard
two-dimensional Euclidean metric and Lebesgue measure. -/
abbrev Plane := ℂ

/-- The [unit circle](goal) is the set of planar points whose Euclidean distance from the origin is one. -/
def unitCircle : Set Plane := {z | ‖z‖ = 1}

/-- For [a planar point](hyp:z), its [signed radial offset](goal) is its Euclidean distance from the
origin minus one; it is negative inside the unit circle and positive outside it. -/
def radialOffset (z : Plane) : ℝ := ‖z‖ - 1

/-- The [type of radial sides adjacent to the unit circle](goal) has an [inside alternative](hyp:inside), representing its interior, and an [outside alternative](hyp:outside), representing its strict exterior. -/
inductive CircleSide where
  | inside
  | outside
  deriving DecidableEq

/-- The [region associated with a radial side](goal) is [the closed interior of the unit circle
for the inside side](step:1), and [the strict exterior of the unit circle for the outside side](step:2). -/
def CircleSide.region : CircleSide → Set Plane
  | .inside => {z | radialOffset z ≤ 0}
  | .outside => {z | 0 < radialOffset z}

/-- For [a real exponent parameter](hyp:κ) and [a planar point](hyp:z), the [radial power weight](goal)
is the absolute radial offset raised to the power $κ-2$. On the unit circle itself the offset is
zero, and zero to a negative power is zero by convention, so for exponents below two the weight is
zero there rather than infinite; this affects only a Lebesgue-null set. -/
def powerWeight (κ : ℝ) (z : Plane) : ℝ := |radialOffset z| ^ (κ - 2)

/-- For [a chosen radial side](hyp:side), [a planar center](hyp:x), and [a real radius](hyp:h),
the [one-sided ball](goal) is the open Euclidean ball with that center and radius, intersected
with the region on the chosen side of the unit circle. -/
def sideBall (side : CircleSide) (x : Plane) (h : ℝ) : Set Plane :=
  ball x h ∩ side.region

/-- [The unit circle](goal) is compact in the Euclidean plane.
@isnad1 id=iscompac.0h0v.s4.9fcf55861c15 from=translated src=- shape=25b03439 vocab=14db6e88
-/
theorem isCompact_unitCircle : IsCompact unitCircle := by
  simpa only [unitCircle, Metric.sphere, Set.mem_ofPred_eq, dist_zero_right] using
    (isCompact_sphere (0 : Plane) 1)

/-- [The unit circle](goal) contains at least one planar point.
@isnad1 id=nonempty.0h0v.s1.80aec5ddb50d from=translated src=- shape=25b03439 vocab=30d28ab8
-/
theorem unitCircle_nonempty : unitCircle.Nonempty := by
  exact ⟨1, by simp [unitCircle]⟩

/-- For [a chosen radial side](hyp:side), [its radial region](goal) is Lebesgue measurable.
@isnad1 id=measurab.0h1v.s2.9d89422d5eb4 from=translated src=- shape=1a6c1393 vocab=bfe948eb
-/
theorem CircleSide.measurableSet_region (side : CircleSide) : MeasurableSet side.region := by
  cases side with
  | inside =>
      exact measurableSet_le (continuous_norm.sub continuous_const).measurable measurable_const
  | outside =>
      exact measurableSet_lt measurable_const (continuous_norm.sub continuous_const).measurable

/-- For [a chosen side](hyp:side), [a planar center](hyp:x), and [a radius](hyp:h), [the
corresponding one-sided ball](goal) is Lebesgue measurable.
@isnad1 id=measurab.0h3v.s3.a9bc4c29d3b6 from=translated src=- shape=2abcec93 vocab=2783a083
-/
theorem measurableSet_sideBall (side : CircleSide) (x : Plane) (h : ℝ) :
    MeasurableSet (sideBall side x h) := by
  exact measurableSet_ball.inter (CircleSide.measurableSet_region side)

/-- When [the exponent κ exceeds two](hyp:hκ), [the radial power weight](goal) is continuous on
the entire Euclidean plane, including the unit circle.
@isnad1 id=continuo.1h1v.s5.307501c4dc55 from=translated src=- shape=cc36a0cc vocab=6f5024fd
-/
theorem continuous_powerWeight {κ : ℝ} (hκ : 2 < κ) : Continuous (powerWeight κ) := by
  exact (Real.continuous_rpow_const (by linarith)).comp
    ((continuous_norm.sub continuous_const).abs)

/-- When [the exponent κ exceeds two](hyp:hκ), [the radial power weight](goal) is Lebesgue
measurable.
@isnad1 id=measurab.1h1v.s4.46da269e60b4 from=translated src=- shape=cc36a0cc vocab=6b43bc10
-/
theorem measurable_powerWeight {κ : ℝ} (hκ : 2 < κ) : Measurable (powerWeight κ) := by
  exact (continuous_powerWeight hκ).measurable

/-- For [an exponent parameter](hyp:κ) and [a planar point](hyp:z), [the radial power weight is
nonnegative](goal).
@isnad1 id=le.0h2v.s4.24b830ed6c3b from=translated src=- shape=25b8bdde vocab=d17f214f
-/
theorem powerWeight_nonneg (κ : ℝ) (z : Plane) : 0 ≤ powerWeight κ z := by
  exact Real.rpow_nonneg (abs_nonneg _) _

/-- When [the exponent κ exceeds two](hyp:hκ), [the radial power weight at a planar point](hyp:z)
[vanishes exactly when that point is on the unit circle](goal).
@isnad1 id=iff.1h2v.s5.daadaad7f349 from=translated src=- shape=7eba8369 vocab=32af2d83
-/
theorem powerWeight_eq_zero_iff {κ : ℝ} (hκ : 2 < κ) (z : Plane) :
    powerWeight κ z = 0 ↔ z ∈ unitCircle := by
  rw [powerWeight, Real.rpow_eq_zero (abs_nonneg _) (by linarith)]
  simp only [abs_eq_zero, radialOffset, unitCircle, Set.mem_ofPred_eq, sub_eq_zero]

/-- When [the exponent κ exceeds two](hyp:hκ), [the radial power weight is integrable over the
one-sided ball determined by the chosen side, center, and radius](goal).
@isnad1 id=integrab.1h4v.s6.6c8b48ad1982 from=translated src=- shape=b05bab9e vocab=80b4def0
-/
theorem integrableOn_powerWeight_sideBall {κ : ℝ} (hκ : 2 < κ)
    (side : CircleSide) (x : Plane) (h : ℝ) :
    IntegrableOn (powerWeight κ) (sideBall side x h) := by
  have hclosed : IntegrableOn (powerWeight κ) (closedBall x h) :=
    (continuous_powerWeight hκ).locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall x h)
  exact Integrable.mono_measure hclosed
    (Measure.restrict_mono
      (inter_subset_left.trans ball_subset_closedBall) le_rfl)

/-- If [a complex multiplier lies on the unit circle](hyp:hu), then [multiplying any planar point
by it](hyp:z) [preserves signed radial offset](goal).
@isnad1 id=eq.1h2v.s4.6f66b2ba72ee from=translated src=- shape=a6ec4c08 vocab=3e2028f2
-/
theorem radialOffset_mul_of_mem_unitCircle {u : Plane} (hu : u ∈ unitCircle) (z : Plane) :
    radialOffset (u * z) = radialOffset z := by
  have hnorm : ‖u‖ = 1 := hu
  simp [radialOffset, hnorm]

/-- If [a complex multiplier lies on the unit circle](hyp:hu), then [multiplication of a planar
point by it](hyp:z) [preserves its distance from the reference point one](goal).
@isnad1 id=eq.1h2v.s5.3e1a1e1f9426 from=translated src=- shape=2077f7d0 vocab=7fa7c5e2
-/
theorem dist_mul_one_of_mem_unitCircle {u : Plane} (hu : u ∈ unitCircle) (z : Plane) :
    dist (u * z) u = dist z 1 := by
  have hnorm : ‖u‖ = 1 := hu
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖u * z - u‖ = ‖u * (z - 1)‖ := by ring_nf
    _ = ‖z - 1‖ := by rw [Complex.norm_mul, hnorm, one_mul]

end Causalean.Mathlib.Analysis.Complex.Circle.WeightedTube
