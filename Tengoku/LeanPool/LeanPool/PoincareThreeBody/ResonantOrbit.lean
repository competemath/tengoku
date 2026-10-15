/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.RotatingEllipse
public import Tengoku
import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Analytic

/-!
# Periodic Kepler ellipses at rational Delaunay resonances

At the action `I₁³ = p / q`, the inertial ellipse makes `q` revolutions while the rotating
frame makes `p` revolutions during the common period `2πp`. This file constructs that orbit and
proves its periodicity exactly.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- Mean motion on the `(p,q)` Kepler resonance. -/
noncomputable def resonantMeanMotion (p q : ℕ) : ℝ :=
  (q : ℝ) / (p : ℝ)

/-- Common period of the inertial ellipse and rotating frame. -/
noncomputable def resonantOrbitPeriod (p : ℕ) : ℝ :=
  2 * Real.pi * p

/-- Mean anomaly along a resonant unperturbed orbit. -/
noncomputable def resonantMeanAnomaly (p q : ℕ) (time : ℝ) : ℝ :=
  resonantMeanMotion p q * time

/-- Eccentric anomaly along a resonant unperturbed orbit. -/
noncomputable def resonantEccentricAnomaly
    (p q : ℕ) (eccentricity time : ℝ) : ℝ :=
  eccentricAnomaly eccentricity (resonantMeanAnomaly p q time)

/-- Position of the resonant Kepler ellipse in the rotating frame. -/
noncomputable def resonantRotatingEllipsePosition
    (p q : ℕ) (eccentricity time : ℝ) : ActionSpace :=
  rotatingEllipsePosition (resonantFirstAction p q) eccentricity
    (resonantEccentricAnomaly p q eccentricity time) time

/-- The resonant position embedded into the four-dimensional phase space. -/
noncomputable def resonantEllipsePhasePoint
    (p q : ℕ) (eccentricity time : ℝ) : PhaseSpace :=
  positionPhasePoint (resonantRotatingEllipsePosition p q eccentricity time)

/--
@isnad1 id=eq.2h2v.s5.6c49c4b45804 from=translated src=- shape=56331341 vocab=92042855
-/
lemma resonantMeanMotion_eq_delaunayFrequency {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    resonantMeanMotion p q =
      delaunayFrequency (resonantFirstAction p q) 0 := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  simp only [resonantMeanMotion, delaunayFrequency, Matrix.cons_val_zero]
  rw [resonantFirstAction_cube hp hq]
  field_simp

/--
@isnad1 id=eq.1h3v.s6.c2391621b30c from=translated src=- shape=ac0e25c9 vocab=42a36f24
-/
lemma resonantMeanAnomaly_add_period {p q : ℕ} (hp : 0 < p) (time : ℝ) :
    resonantMeanAnomaly p q (time + resonantOrbitPeriod p) =
      resonantMeanAnomaly p q time + q * (2 * Real.pi) := by
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  unfold resonantMeanAnomaly resonantMeanMotion resonantOrbitPeriod
  field_simp

/--
@isnad1 id=eq.3h4v.s6.91d6a6a416e8 from=translated src=- shape=530e6565 vocab=65e87a3e
-/
lemma resonantEccentricAnomaly_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantEccentricAnomaly p q eccentricity (time + resonantOrbitPeriod p) =
      resonantEccentricAnomaly p q eccentricity time + q * (2 * Real.pi) := by
  unfold resonantEccentricAnomaly
  rw [resonantMeanAnomaly_add_period hp,
    eccentricAnomaly_add_nat_mul_two_pi q heccentricity heccentricityOne]

/--
@isnad1 id=analytic.0h3v.s5.0f49c28ad72d from=translated src=- shape=6e3afc3f vocab=45979946
-/
theorem analyticAt_resonantMeanAnomaly (p q : ℕ) (time : ℝ) :
    AnalyticAt ℝ (resonantMeanAnomaly p q) time := by
  have hid : AnalyticAt ℝ id time := analyticAt_id
  have hraw := hid.const_smul (c := resonantMeanMotion p q)
  apply hraw.congr
  filter_upwards [] with argument
  simp [resonantMeanAnomaly, smul_eq_mul]

/--
@isnad1 id=analytic.2h4v.s6.9305d8a815b0 from=translated src=- shape=d25ca660 vocab=93618eb4
-/
theorem analyticAt_resonantEccentricAnomaly (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (resonantEccentricAnomaly p q eccentricity) time := by
  exact (analyticAt_eccentricAnomaly
    (meanAnomaly := resonantMeanAnomaly p q time) heccentricity heccentricityOne).comp
      (analyticAt_resonantMeanAnomaly p q time)

/--
@isnad1 id=analytic.2h5v.s6.e4cf8d5b8da8 from=translated src=- shape=1e5ad6f4 vocab=54a0d776
-/
theorem analyticAt_resonantRotatingEllipsePosition_coordinate
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    AnalyticAt ℝ (fun argument ↦
      resonantRotatingEllipsePosition p q eccentricity argument coordinate) time := by
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let firstAction := resonantFirstAction p q
  have hanomaly : AnalyticAt ℝ anomaly time :=
    analyticAt_resonantEccentricAnomaly p q heccentricity heccentricityOne
  have hcosAnomaly := Real.analyticAt_cos.comp hanomaly
  have hsinAnomaly := Real.analyticAt_sin.comp hanomaly
  have heccentricityConstant : AnalyticAt ℝ (fun _ : ℝ ↦ eccentricity) time :=
    analyticAt_const
  have hxRaw := (hcosAnomaly.sub heccentricityConstant).const_smul
    (c := firstAction ^ 2)
  have hx : AnalyticAt ℝ
      (fun argument ↦ firstAction ^ 2 * (Real.cos (anomaly argument) - eccentricity))
      time := by
    apply hxRaw.congr
    filter_upwards [] with argument
    simp [smul_eq_mul]
  have hyRaw := hsinAnomaly.const_smul
    (c := firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2))
  have hy : AnalyticAt ℝ
      (fun argument ↦ firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
        Real.sin (anomaly argument)) time := by
    apply hyRaw.congr
    filter_upwards [] with argument
    simp [smul_eq_mul]
  have hcosTime : AnalyticAt ℝ Real.cos time := Real.analyticAt_cos
  have hsinTime : AnalyticAt ℝ Real.sin time := Real.analyticAt_sin
  fin_cases coordinate
  · change AnalyticAt ℝ
      (fun argument ↦ Real.cos argument *
          (firstAction ^ 2 * (Real.cos (anomaly argument) - eccentricity)) +
        Real.sin argument *
          (firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
            Real.sin (anomaly argument))) time
    exact (hcosTime.mul hx).add (hsinTime.mul hy)
  · change AnalyticAt ℝ
      (fun argument ↦ -Real.sin argument *
          (firstAction ^ 2 * (Real.cos (anomaly argument) - eccentricity)) +
        Real.cos argument *
          (firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
            Real.sin (anomaly argument))) time
    exact (hsinTime.neg.mul hx).add (hcosTime.mul hy)

/-- Away from a collision with the unit primary, the disturbing function restricted to a resonant
ellipse is real analytic in time.
@isnad1 id=analytic.5h4v.s7.2007993dcc9f from=translated src=- shape=6a58ebfb vocab=a5631458
-/
theorem analyticAt_firstMassPerturbation_resonantOrbit
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimary :
      (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
          (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0) :
    AnalyticAt ℝ (fun argument ↦ firstMassPerturbation
      (resonantEllipsePhasePoint p q eccentricity argument)) time := by
  let x : ℝ → ℝ := fun argument ↦
    resonantRotatingEllipsePosition p q eccentricity argument 0
  let y : ℝ → ℝ := fun argument ↦
    resonantRotatingEllipsePosition p q eccentricity argument 1
  have hx : AnalyticAt ℝ x time :=
    analyticAt_resonantRotatingEllipsePosition_coordinate p q heccentricity
      heccentricityOne 0
  have hy : AnalyticAt ℝ y time :=
    analyticAt_resonantRotatingEllipsePosition_coordinate p q heccentricity
      heccentricityOne 1
  have horiginSq : AnalyticAt ℝ (fun argument ↦ x argument ^ 2 + y argument ^ 2)
      time := (hx.pow 2).add (hy.pow 2)
  have hfirstAction : resonantFirstAction p q ≠ 0 :=
    (resonantFirstAction_pos hp hq).ne'
  have hradius := eccentricRadius_pos (anomaly :=
      resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
    heccentricityOne
  have horiginValue : 0 < x time ^ 2 + y time ^ 2 := by
    change 0 <
      (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
          (resonantEccentricAnomaly p q eccentricity time) time 0) ^ 2 +
        (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
          (resonantEccentricAnomaly p q eccentricity time) time 1) ^ 2
    rw [rotatingEllipsePosition_sq heccentricity heccentricityOne.le]
    exact sq_pos_of_pos hradius
  have hinverseOrigin : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt (x argument ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ x argument ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt horiginValue).comp
      (f := fun argument ↦ x argument ^ 2 + y argument ^ 2) horiginSq
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) time := analyticAt_const
  have hprimarySq : AnalyticAt ℝ
      (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) time :=
    ((hx.sub hone).pow 2).add (hy.pow 2)
  have hprimaryValue : 0 < (x time - 1) ^ 2 + y time ^ 2 := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hprimary)
  have hinversePrimary : AnalyticAt ℝ
      (fun argument ↦ 1 / Real.sqrt ((x argument - 1) ^ 2 + y argument ^ 2)) time := by
    change AnalyticAt ℝ
      ((fun value : ℝ ↦ 1 / Real.sqrt value) ∘
        (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2)) time
    exact (analyticAt_inv_sqrt hprimaryValue).comp
      (f := fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) hprimarySq
  have hraw := hinverseOrigin.add (hx.mul (hinverseOrigin.pow 3)) |>.sub hinversePrimary
  apply hraw.congr
  filter_upwards [] with argument
  simp [x, y, resonantEllipsePhasePoint, positionPhasePoint, firstMassPerturbation,
    div_eq_mul_inv]

/--
@isnad1 id=interval.5h5v.s7.cd88834c8960 from=translated src=- shape=1c8940bc vocab=103bc2a1
-/
theorem intervalIntegrable_firstMassPerturbation_resonantOrbit
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimary : ∀ time ∈ Set.uIcc start finish,
      (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
          (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0) :
    IntervalIntegrable
      (fun time ↦ firstMassPerturbation
        (resonantEllipsePhasePoint p q eccentricity time))
      MeasureTheory.volume start finish := by
  apply ContinuousOn.intervalIntegrable
  intro time htime
  exact (analyticAt_firstMassPerturbation_resonantOrbit hp hq heccentricity
    heccentricityOne (hprimary time htime)).continuousAt.continuousWithinAt

/--
@isnad1 id=ne.3h4v.s7.6417739db030 from=translated src=- shape=7e991c9e vocab=fda24dc9
-/
lemma resonantRotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    {p q : ℕ} {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
        (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0 := by
  exact rotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one heccentricity
    heccentricityOne hapoapsis

/--
@isnad1 id=analytic.5h4v.s7.61970df2c1ae from=translated src=- shape=ec7ffd04 vocab=fcc827b9
-/
theorem analyticAt_firstMassPerturbation_resonantOrbit_of_apoapsis_lt_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (fun argument ↦ firstMassPerturbation
      (resonantEllipsePhasePoint p q eccentricity argument)) time := by
  exact analyticAt_firstMassPerturbation_resonantOrbit hp hq heccentricity
    heccentricityOne
    (resonantRotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
      heccentricity heccentricityOne hapoapsis)

/--
@isnad1 id=interval.5h5v.s7.42a0094d3ea2 from=translated src=- shape=3d15f330 vocab=0aabfac1
-/
theorem intervalIntegrable_firstMassPerturbation_resonantOrbit_of_apoapsis_lt_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity start finish : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    IntervalIntegrable
      (fun time ↦ firstMassPerturbation
        (resonantEllipsePhasePoint p q eccentricity time))
      MeasureTheory.volume start finish := by
  apply intervalIntegrable_firstMassPerturbation_resonantOrbit hp hq heccentricity
    heccentricityOne
  intro time _
  exact resonantRotatingEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
    heccentricity heccentricityOne hapoapsis

/--
@isnad1 id=mem.5h4v.s7.9ddafe9213f6 from=translated src=- shape=fade18ac vocab=d32f50b7
-/
lemma resonantEllipsePhasePoint_collisionFree_mass_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hprimary :
      (resonantRotatingEllipsePosition p q eccentricity time 0 - 1) ^ 2 +
          (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0) :
    (0, resonantEllipsePhasePoint p q eccentricity time) ∈
      collisionFree := by
  constructor
  · simpa [firstPrimaryDistanceSq,
      resonantEllipsePhasePoint, positionPhasePoint] using hprimary
  · have hfirstAction : resonantFirstAction p q ≠ 0 :=
      (resonantFirstAction_pos hp hq).ne'
    have hradius := eccentricRadius_pos (anomaly :=
        resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
      heccentricityOne
    have horigin :
        (resonantRotatingEllipsePosition p q eccentricity time 0) ^ 2 +
            (resonantRotatingEllipsePosition p q eccentricity time 1) ^ 2 ≠ 0 := by
      change
        (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
            (resonantEccentricAnomaly p q eccentricity time) time 0) ^ 2 +
          (rotatingEllipsePosition (resonantFirstAction p q) eccentricity
            (resonantEccentricAnomaly p q eccentricity time) time 1) ^ 2 ≠ 0
      rw [rotatingEllipsePosition_sq heccentricity heccentricityOne.le]
      exact (sq_pos_of_pos hradius).ne'
    simpa [secondPrimaryDistanceSq,
      resonantEllipsePhasePoint, positionPhasePoint] using horigin

/-- A rational Kepler resonance gives a genuinely periodic orbit in the rotating frame.
@isnad1 id=eq.3h4v.s5.bd50c6f27403 from=translated src=- shape=12dc61a4 vocab=d2ae8e51
-/
theorem resonantRotatingEllipsePosition_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantRotatingEllipsePosition p q eccentricity (time + resonantOrbitPeriod p) =
      resonantRotatingEllipsePosition p q eccentricity time := by
  unfold resonantRotatingEllipsePosition rotatingEllipsePosition positionInRotatingFrame
  rw [resonantEccentricAnomaly_add_period hp heccentricity heccentricityOne]
  unfold resonantOrbitPeriod
  have hperiod : 2 * Real.pi * (p : ℝ) = (p : ℝ) * (2 * Real.pi) := by ring
  rw [hperiod]
  simp [inertialEllipsePosition]

/--
@isnad1 id=eq.3h4v.s5.74662d94bbb9 from=translated src=- shape=12dc61a4 vocab=f5ed6e54
-/
lemma resonantEllipsePhasePoint_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    resonantEllipsePhasePoint p q eccentricity (time + resonantOrbitPeriod p) =
      resonantEllipsePhasePoint p q eccentricity time := by
  unfold resonantEllipsePhasePoint
  rw [resonantRotatingEllipsePosition_add_period hp heccentricity heccentricityOne]

/-- The disturbing function restricted to a resonant ellipse has the common resonant period.
@isnad1 id=eq.3h4v.s5.9c9b6659f4db from=translated src=- shape=488c8f00 vocab=0cc4d4e6
-/
lemma firstMassPerturbation_resonantOrbit_periodic {p q : ℕ} (hp : 0 < p)
    {eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    firstMassPerturbation
        (resonantEllipsePhasePoint p q eccentricity (time + resonantOrbitPeriod p)) =
      firstMassPerturbation (resonantEllipsePhasePoint p q eccentricity time) := by
  rw [resonantEllipsePhasePoint_add_period hp heccentricity heccentricityOne]

end LeanPool.PoincareThreeBody
