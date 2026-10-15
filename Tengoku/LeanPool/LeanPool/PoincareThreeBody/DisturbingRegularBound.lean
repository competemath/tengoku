/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.CollisionIntegralBlowup
public import Tengoku

/-!
# Uniform control of the regular disturbing terms near collision

The two nonsingular terms in the first mass perturbation stay uniformly bounded as an interior
resonant ellipse approaches its apoapsis collision boundary.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- The part of the resonant disturbing function which is regular at the unit primary. -/
noncomputable def resonantRegularPart
    (p q : ℕ) (eccentricity orientation time : ℝ) : ℝ :=
  let position := orientedResonantEllipsePosition p q eccentricity orientation time
  1 / Real.sqrt (position 0 ^ 2 + position 1 ^ 2) +
    position 0 / (Real.sqrt (position 0 ^ 2 + position 1 ^ 2)) ^ 3

/--
@isnad1 id=eq.0h5v.s5.ec5304ce065d from=translated src=- shape=bca49e29 vocab=f53e8c38
-/
lemma resonantDisturbingFunction_eq_regularPart_sub_primaryInverse
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    resonantDisturbingFunction p q eccentricity orientation time =
      resonantRegularPart p q eccentricity orientation time -
        resonantPrimaryInverse p q eccentricity orientation time := by
  simp [resonantDisturbingFunction, resonantRegularPart, resonantPrimaryInverse,
    orientedResonantEllipsePhasePoint, positionPhasePoint, firstMassPerturbation]

/--
@isnad1 id=eq.4h5v.s7.f975a3058873 from=translated src=- shape=dd2b2d76 vocab=7d632753
-/
theorem sqrt_orientedResonantEllipse_origin_sq
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    Real.sqrt
        (orientedResonantEllipsePosition p q eccentricity orientation time 0 ^ 2 +
          orientedResonantEllipsePosition p q eccentricity orientation time 1 ^ 2) =
      eccentricRadius (resonantFirstAction p q) eccentricity
        (resonantEccentricAnomaly p q eccentricity time) := by
  rw [orientedResonantEllipsePosition_sq heccentricity heccentricityOne.le]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos]
  exact eccentricRadius_pos (resonantFirstAction_pos hp hq).ne'
    heccentricity heccentricityOne

/-- The pericenter radius at the collision boundary is `2a - 1`, which is positive precisely in
the interior band `a > 1/2`.
@isnad1 id=lt.1h2v.s6.33e50d3a4275 from=translated src=- shape=593f49a3 vocab=7714bb13
-/
theorem collision_radius_floor_pos
    {p q : ℕ} (haxisHalf : 1 / 2 < resonantSemimajorAxis p q) :
    0 < 2 * resonantSemimajorAxis p q - 1 := by
  linarith

/-- Every radius before collision is bounded below by the boundary pericenter radius.
@isnad1 id=le.5h4v.s6.4838c9c6f0a6 from=translated src=- shape=91444b61 vocab=90ef1f35
-/
theorem collision_radius_floor_le_eccentricRadius
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    {eccentricity anomaly : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityBoundary : eccentricity ≤ resonantCollisionEccentricity p q) :
    2 * resonantSemimajorAxis p q - 1 ≤
      eccentricRadius (resonantFirstAction p q) eccentricity anomaly := by
  let semimajorAxis := resonantSemimajorAxis p q
  have haxisPositive : 0 < semimajorAxis := resonantSemimajorAxis_pos hp hq
  have hcos : eccentricity * Real.cos anomaly ≤ eccentricity :=
    mul_le_of_le_one_right heccentricity (Real.cos_le_one anomaly)
  have hboundary :
      semimajorAxis * (1 - resonantCollisionEccentricity p q) =
        2 * semimajorAxis - 1 := by
    dsimp [semimajorAxis]
    unfold resonantCollisionEccentricity
    field_simp [haxisPositive.ne']
    ring
  calc
    2 * semimajorAxis - 1 =
        semimajorAxis * (1 - resonantCollisionEccentricity p q) := hboundary.symm
    _ ≤ semimajorAxis * (1 - eccentricity) := by gcongr
    _ ≤ semimajorAxis * (1 - eccentricity * Real.cos anomaly) := by gcongr
    _ = eccentricRadius (resonantFirstAction p q) eccentricity anomaly := by
      rfl

/--
@isnad1 id=lt.3h3v.s6.d173dd71698d from=translated src=- shape=7429227d vocab=150786d5
-/
theorem resonant_apoapsis_lt_one_of_eccentricity_lt_collision
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity : ℝ}
    (heccentricityBoundary : eccentricity < resonantCollisionEccentricity p q) :
    resonantSemimajorAxis p q * (1 + eccentricity) < 1 := by
  have haxisPositive := resonantSemimajorAxis_pos hp hq
  calc
    resonantSemimajorAxis p q * (1 + eccentricity) <
        resonantSemimajorAxis p q *
          (1 + resonantCollisionEccentricity p q) := by gcongr
    _ = 1 := by
      unfold resonantCollisionEccentricity
      field_simp [haxisPositive.ne']
      ring

/-- Explicit uniform absolute bound for the regular part throughout the pre-collision family.
@isnad1 id=le.6h5v.s7.5147021fec25 from=translated src=- shape=4b61caa4 vocab=498ca72e
-/
theorem abs_resonantRegularPart_le_collision_bound
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (heccentricityBoundary : eccentricity ≤ resonantCollisionEccentricity p q) :
    |resonantRegularPart p q eccentricity orientation time| ≤
      1 / (2 * resonantSemimajorAxis p q - 1) +
        1 / (2 * resonantSemimajorAxis p q - 1) ^ 2 := by
  let position := orientedResonantEllipsePosition p q eccentricity orientation time
  let radius := eccentricRadius (resonantFirstAction p q) eccentricity
    (resonantEccentricAnomaly p q eccentricity time)
  let floor := 2 * resonantSemimajorAxis p q - 1
  have hradiusPositive : 0 < radius := eccentricRadius_pos
    (resonantFirstAction_pos hp hq).ne' heccentricity heccentricityOne
  have hfloorPositive : 0 < floor := collision_radius_floor_pos haxisHalf
  have hfloorRadius : floor ≤ radius :=
    collision_radius_floor_le_eccentricRadius hp hq haxisHalf heccentricity
      heccentricityBoundary
  have hpositionSq : position 0 ^ 2 + position 1 ^ 2 = radius ^ 2 := by
    exact orientedResonantEllipsePosition_sq heccentricity heccentricityOne.le
  have hxSq : position 0 ^ 2 ≤ radius ^ 2 := by
    nlinarith [sq_nonneg (position 1)]
  have hx : |position 0| ≤ radius :=
    abs_le_of_sq_le_sq hxSq hradiusPositive.le
  have hinverse : 1 / radius ≤ 1 / floor :=
    one_div_le_one_div_of_le hfloorPositive hfloorRadius
  have hinverseSq : 1 / radius ^ 2 ≤ 1 / floor ^ 2 := by
    gcongr
  have hxTerm : |position 0 / radius ^ 3| ≤ 1 / radius ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos hradiusPositive]
    calc
      |position 0| / radius ^ 3 ≤ radius / radius ^ 3 := by gcongr
      _ = 1 / radius ^ 2 := by
        field_simp [hradiusPositive.ne']
  unfold resonantRegularPart
  dsimp only
  rw [sqrt_orientedResonantEllipse_origin_sq hp hq heccentricity heccentricityOne]
  calc
    |1 / radius + position 0 / radius ^ 3| ≤
        |1 / radius| + |position 0 / radius ^ 3| := abs_add_le _ _
    _ ≤ 1 / radius + 1 / radius ^ 2 := by
      rw [abs_of_pos (one_div_pos.mpr hradiusPositive)]
      gcongr
    _ ≤ 1 / floor + 1 / floor ^ 2 := add_le_add hinverse hinverseSq

/--
@isnad1 id=interval.5h6v.s6.b009cf39eef2 from=translated src=- shape=315212c3 vocab=2585b3d7
-/
theorem intervalIntegrable_resonantRegularPart
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1) :
    IntervalIntegrable (resonantRegularPart p q eccentricity orientation)
      MeasureTheory.volume start finish := by
  have hdisturbing := intervalIntegrable_resonantDisturbingFunction hp hq
    (orientation := orientation) (start := start) (finish := finish)
    heccentricity heccentricityOne (by
      simpa [resonantSemimajorAxis] using hapoapsis)
  have hprimary := (continuous_resonantPrimaryInverse
    (p := p) (q := q) (eccentricity := eccentricity) (orientation := orientation)
    heccentricity heccentricityOne hapoapsis).intervalIntegrable
      (μ := MeasureTheory.volume) start finish
  apply (hdisturbing.add hprimary).congr
  intro time _
  change resonantDisturbingFunction p q eccentricity orientation time +
    resonantPrimaryInverse p q eccentricity orientation time =
      resonantRegularPart p q eccentricity orientation time
  rw [resonantDisturbingFunction_eq_regularPart_sub_primaryInverse]
  ring

/-- The integral of the regular part is uniformly bounded throughout the pre-collision family.
@isnad1 id=le.6h4v.s7.268865a25016 from=translated src=- shape=44ca3936 vocab=3ae660b3
-/
theorem abs_integral_resonantRegularPart_le_collision_bound
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (heccentricityBoundary : eccentricity < resonantCollisionEccentricity p q) :
    |∫ time in 0..resonantOrbitPeriod p,
        resonantRegularPart p q eccentricity orientation time| ≤
      resonantOrbitPeriod p *
        (1 / (2 * resonantSemimajorAxis p q - 1) +
          1 / (2 * resonantSemimajorAxis p q - 1) ^ 2) := by
  let bound := 1 / (2 * resonantSemimajorAxis p q - 1) +
    1 / (2 * resonantSemimajorAxis p q - 1) ^ 2
  have hapoapsis := resonant_apoapsis_lt_one_of_eccentricity_lt_collision
    hp hq heccentricityBoundary
  have hperiod : 0 ≤ resonantOrbitPeriod p := by
    unfold resonantOrbitPeriod
    positivity
  have hregular := intervalIntegrable_resonantRegularPart hp hq
    (orientation := orientation) (start := 0) (finish := resonantOrbitPeriod p)
      heccentricity heccentricityOne hapoapsis
  have habsolute : IntervalIntegrable
      (fun time ↦ |resonantRegularPart p q eccentricity orientation time|)
      MeasureTheory.volume 0 (resonantOrbitPeriod p) := by
    simpa only [Real.norm_eq_abs] using hregular.norm
  calc
    |∫ time in 0..resonantOrbitPeriod p,
        resonantRegularPart p q eccentricity orientation time| ≤
        ∫ time in 0..resonantOrbitPeriod p,
          |resonantRegularPart p q eccentricity orientation time| :=
      intervalIntegral.abs_integral_le_integral_abs hperiod
    _ ≤ ∫ _time in 0..resonantOrbitPeriod p, bound := by
      apply intervalIntegral.integral_mono_on hperiod habsolute
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ bound)
          MeasureTheory.volume 0 (resonantOrbitPeriod p))
      intro time _
      exact abs_resonantRegularPart_le_collision_bound hp hq haxisHalf
        heccentricity heccentricityOne heccentricityBoundary.le
    _ = resonantOrbitPeriod p * bound := by
      rw [intervalIntegral.integral_const]
      ring

end LeanPool.PoincareThreeBody
