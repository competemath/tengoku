/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.KeplerOrbit
public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Perturbation
public import Tengoku

/-!
# Elliptic Kepler positions in the rotating frame

The eccentric-anomaly ellipse has a simple Cartesian parameterization in the inertial frame.
Rotating it through minus the physical time gives the position used in the circular restricted
three-body Hamiltonian. This file verifies the radius and distance identities needed to restrict
the first mass perturbation to a resonant Kepler orbit.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- Cartesian position on an inertial Kepler ellipse, with periapsis on the positive x-axis. -/
noncomputable def inertialEllipsePosition
    (firstAction eccentricity anomaly : ℝ) : ActionSpace :=
  ![firstAction ^ 2 * (Real.cos anomaly - eccentricity),
    firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) * Real.sin anomaly]

/-- A planar position expressed in coordinates rotating counterclockwise through angle `time`. -/
noncomputable def positionInRotatingFrame (time : ℝ) (position : ActionSpace) : ActionSpace :=
  ![Real.cos time * position 0 + Real.sin time * position 1,
    -Real.sin time * position 0 + Real.cos time * position 1]

/-- Position of the Kepler ellipse in the rotating frame. -/
noncomputable def rotatingEllipsePosition
    (firstAction eccentricity anomaly time : ℝ) : ActionSpace :=
  positionInRotatingFrame time (inertialEllipsePosition firstAction eccentricity anomaly)

/-- Embed a planar position into phase space with zero placeholder momenta. The first mass
perturbation depends only on position, so these momentum entries are immaterial. -/
def positionPhasePoint (position : ActionSpace) : PhaseSpace :=
  ![position 0, position 1, 0, 0]

/-- A rotating elliptic position embedded in the restricted three-body phase space. -/
noncomputable def rotatingEllipsePhasePoint
    (firstAction eccentricity anomaly time : ℝ) : PhaseSpace :=
  positionPhasePoint (rotatingEllipsePosition firstAction eccentricity anomaly time)

/--
@isnad1 id=eq.2h3v.s7.34f867f051a3 from=translated src=- shape=d3c79f91 vocab=1e57271d
-/
lemma inertialEllipsePosition_sq {firstAction eccentricity anomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    (inertialEllipsePosition firstAction eccentricity anomaly 0) ^ 2 +
        (inertialEllipsePosition firstAction eccentricity anomaly 1) ^ 2 =
      (eccentricRadius firstAction eccentricity anomaly) ^ 2 := by
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 = 1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq anomaly
  have hcos : Real.cos anomaly ^ 2 = 1 - Real.sin anomaly ^ 2 := by
    nlinarith
  simp only [inertialEllipsePosition, eccentricRadius, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring_nf
  rw [hsqrt, hcos]
  ring

/--
@isnad1 id=eq.0h2v.s7.15633e03f2a6 from=translated src=- shape=c24a0130 vocab=cf1d45ab
-/
lemma positionInRotatingFrame_sq (time : ℝ) (position : ActionSpace) :
    (positionInRotatingFrame time position 0) ^ 2 +
        (positionInRotatingFrame time position 1) ^ 2 =
      (position 0) ^ 2 + (position 1) ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq time
  simp only [positionInRotatingFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ((position 0) ^ 2 + (position 1) ^ 2) * htrig

/--
@isnad1 id=eq.0h3v.s4.680c358a6582 from=translated src=- shape=7177eae1 vocab=56fe8e24
-/
lemma positionInRotatingFrame_add (firstAngle secondAngle : ℝ) (position : ActionSpace) :
    positionInRotatingFrame (firstAngle + secondAngle) position =
      positionInRotatingFrame firstAngle (positionInRotatingFrame secondAngle position) := by
  unfold positionInRotatingFrame
  funext coordinate
  fin_cases coordinate <;> simp [Real.cos_add, Real.sin_add] <;> ring

/--
@isnad1 id=eq.2h4v.s7.f5df44a88589 from=translated src=- shape=d67825cb vocab=e5280879
-/
lemma rotatingEllipsePosition_sq {firstAction eccentricity anomaly time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    (rotatingEllipsePosition firstAction eccentricity anomaly time 0) ^ 2 +
        (rotatingEllipsePosition firstAction eccentricity anomaly time 1) ^ 2 =
      (eccentricRadius firstAction eccentricity anomaly) ^ 2 := by
  rw [rotatingEllipsePosition, positionInRotatingFrame_sq,
    inertialEllipsePosition_sq heccentricity heccentricityOne]

/-- An ellipse whose apoapsis is strictly inside the unit circle cannot meet the unit primary.
@isnad1 id=ne.3h4v.s7.4fe6d37f26d3 from=translated src=- shape=41edcf71 vocab=f3332bbd
-/
lemma rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    {firstAction eccentricity anomaly time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    (rotatingEllipsePosition firstAction eccentricity anomaly time 0 - 1) ^ 2 +
        (rotatingEllipsePosition firstAction eccentricity anomaly time 1) ^ 2 ≠ 0 := by
  let x := rotatingEllipsePosition firstAction eccentricity anomaly time 0
  let y := rotatingEllipsePosition firstAction eccentricity anomaly time 1
  let radius := eccentricRadius firstAction eccentricity anomaly
  have hradiusUpper : radius < 1 :=
    lt_of_le_of_lt (eccentricRadius_le_apoapsis_bound heccentricity) hapoapsis
  have hradiusNonneg : 0 ≤ radius := by
    unfold radius eccentricRadius
    exact mul_nonneg (sq_nonneg firstAction)
      (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).le
  have hpositionSq : x ^ 2 + y ^ 2 = radius ^ 2 :=
    rotatingEllipsePosition_sq heccentricity heccentricityOne.le
  intro hcollision
  have hxSquare : (x - 1) ^ 2 = 0 := by nlinarith [sq_nonneg y]
  have hySquare : y ^ 2 = 0 := by nlinarith [sq_nonneg (x - 1)]
  have hx : x = 1 := by nlinarith [sq_eq_zero_iff.mp hxSquare]
  have hy : y = 0 := sq_eq_zero_iff.mp hySquare
  rw [hx, hy] at hpositionSq
  nlinarith

/--
@isnad1 id=eq.0h1v.s7.09aa7e06e58e from=translated src=- shape=8dbbc51a vocab=f24e40c3
-/
lemma primaryDistanceSq_positionPhasePoint (position : ActionSpace) :
    ((positionPhasePoint position 0 - 1) ^ 2 + (positionPhasePoint position 1) ^ 2) =
      ((position 0) ^ 2 + (position 1) ^ 2) - 2 * position 0 + 1 := by
  simp [positionPhasePoint]
  ring

/-- Restriction of the first mass perturbation to an elliptic Kepler position, written in terms of
its radius and rotating x-coordinate.
@isnad1 id=eq.3h4v.s7.c7141aabf9c6 from=translated src=- shape=ea4e6aeb vocab=5ec313a2
-/
theorem firstMassPerturbation_rotatingEllipse
    {firstAction eccentricity anomaly time : ℝ} (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    firstMassPerturbation
        (rotatingEllipsePhasePoint firstAction eccentricity anomaly time) =
      1 / eccentricRadius firstAction eccentricity anomaly +
        rotatingEllipsePosition firstAction eccentricity anomaly time 0 /
          (eccentricRadius firstAction eccentricity anomaly) ^ 3 -
        1 / Real.sqrt
          ((eccentricRadius firstAction eccentricity anomaly) ^ 2 -
            2 * rotatingEllipsePosition firstAction eccentricity anomaly time 0 + 1) := by
  let position := rotatingEllipsePosition firstAction eccentricity anomaly time
  let radius := eccentricRadius firstAction eccentricity anomaly
  have hradius : 0 < radius :=
    eccentricRadius_pos hfirstAction heccentricity heccentricityOne
  have hpositionSq : (position 0) ^ 2 + (position 1) ^ 2 = radius ^ 2 :=
    rotatingEllipsePosition_sq heccentricity heccentricityOne.le
  have hsqrt : Real.sqrt ((position 0) ^ 2 + (position 1) ^ 2) = radius := by
    rw [hpositionSq, Real.sqrt_sq_eq_abs, abs_of_pos hradius]
  have hdistance :
      (position 0 - 1) ^ 2 + (position 1) ^ 2 =
        radius ^ 2 - 2 * position 0 + 1 := by
    nlinarith [hpositionSq]
  change
    1 / Real.sqrt ((position 0) ^ 2 + (position 1) ^ 2) +
          position 0 / (Real.sqrt ((position 0) ^ 2 + (position 1) ^ 2)) ^ 3 -
        1 / Real.sqrt ((position 0 - 1) ^ 2 + (position 1) ^ 2) =
      1 / radius + position 0 / radius ^ 3 -
        1 / Real.sqrt (radius ^ 2 - 2 * position 0 + 1)
  rw [hsqrt, hdistance]

/-- Equivalent source form of the restricted perturbation, combining its first two terms over
the cube of the Kepler radius.
@isnad1 id=eq.3h4v.s7.bee147eb773d from=translated src=- shape=251d6125 vocab=5ec313a2
-/
theorem firstMassPerturbation_rotatingEllipse_sourceForm
    {firstAction eccentricity anomaly time : ℝ} (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    firstMassPerturbation
        (rotatingEllipsePhasePoint firstAction eccentricity anomaly time) =
      ((eccentricRadius firstAction eccentricity anomaly) ^ 2 +
          rotatingEllipsePosition firstAction eccentricity anomaly time 0) /
          (eccentricRadius firstAction eccentricity anomaly) ^ 3 -
        1 / Real.sqrt
          ((eccentricRadius firstAction eccentricity anomaly) ^ 2 -
            2 * rotatingEllipsePosition firstAction eccentricity anomaly time 0 + 1) := by
  rw [firstMassPerturbation_rotatingEllipse hfirstAction heccentricity heccentricityOne]
  have hradius := eccentricRadius_pos (anomaly := anomaly) hfirstAction heccentricity
    heccentricityOne
  field_simp [hradius.ne']

end LeanPool.PoincareThreeBody
