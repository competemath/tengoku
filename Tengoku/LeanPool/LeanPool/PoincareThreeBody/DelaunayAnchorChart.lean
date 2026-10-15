/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.GlobalEnergySection
public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.ActionPoisson
import Tengoku.LeanPool.LeanPool.PoincareThreeBody.ActionFactorization
import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Analytic
import Tengoku.LeanPool.LeanPool.PoincareThreeBody.KeplerHamiltonian
public import Tengoku

/-!
# A local Delaunay chart at the rational elliptic anchor

We combine the two Delaunay actions, eccentric anomaly, and apsidal orientation into a
four-dimensional chart.  Its derivative at the rational anchor is nonsingular, so its image
contains a phase-space neighborhood of the anchor.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- Action and angle variables for the local four-dimensional chart. -/
abbrev DelaunayAnchorParameters := ActionSpace × (ℝ × ℝ)

/-- The action pair at the rational energy `-2` anchor. -/
noncomputable def delaunayAnchorAction : ActionSpace :=
  ![1 / Real.sqrt 3, (1 / 2 : ℝ)]

/-- Parameters corresponding to the rational phase point `(0, 1/6, -3, 0)`. -/
noncomputable def delaunayAnchorParameters : DelaunayAnchorParameters :=
  (delaunayAnchorAction, 0, Real.pi / 2)

/-- Full local Delaunay chart using eccentric anomaly as its first angle. -/
noncomputable def delaunayAnchorChart
    (parameters : DelaunayAnchorParameters) : PhaseSpace :=
  delaunayActionSectionAtAnomaly parameters.2.1 parameters.2.2 parameters.1

/-- The same anchor torus, parametrized by mean anomaly and apsidal orientation. -/
noncomputable def delaunayAnchorMeanAngleChart (angles : ℝ × ℝ) : PhaseSpace :=
  liftedDelaunayPhasePoint (1 / Real.sqrt 3) (1 / 2) angles.1 angles.2

/-- The angle pair at the rational anchor. -/
noncomputable def delaunayAnchorMeanAngles : ℝ × ℝ :=
  (0, Real.pi / 2)

/--
@isnad1 id=analytic.0h0v.s7.4dbbf90134b0 from=translated src=- shape=c1acf293 vocab=7bbc5cf1
-/
theorem analyticAt_delaunayAnchorMeanAngleChart :
    AnalyticAt ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles := by
  exact analyticAt_liftedDelaunayPhasePoint_angles (by norm_num) (by norm_num) _

/-- Hamiltonian vectors commute with pulling an action covector back along an action
derivative.
@isnad1 id=eq.0h2v.s8.86537a15f1d4 from=translated src=- shape=eaac2885 vocab=7401c86d
-/
theorem phaseHamiltonianVector_actionCovector_comp
    (actionDerivative : PhaseSpace →L[ℝ] ActionSpace) (vector : ActionSpace) :
    phaseHamiltonianVector ((actionCovector vector).comp actionDerivative) =
      actionHamiltonianTangentMap actionDerivative vector := by
  have hcovector : (actionCovector vector).comp actionDerivative =
      vector 0 • actionDerivativeCovector actionDerivative 0 +
        vector 1 • actionDerivativeCovector actionDerivative 1 := by
    apply ContinuousLinearMap.ext
    intro direction
    simp [actionCovector, actionDerivativeCovector]
    ring
  rw [hcovector, phaseHamiltonianVector_add,
    phaseHamiltonianVector_smul, phaseHamiltonianVector_smul]
  rfl

/-- The Hamiltonian vector of the mass-zero Hamiltonian differential is its explicit rotating
Kepler vector field.
@isnad1 id=eq.1h1v.s7.a69c0cbc7e88 from=translated src=- shape=898ccefc vocab=ad5a680a
-/
theorem phaseHamiltonianVector_fderiv_hamiltonian_zero
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0) :
    phaseHamiltonianVector (fderiv ℝ (hamiltonian 0) state) =
      rotatingKeplerVectorField state := by
  rw [fderiv_hamiltonian_zero hposition]
  funext coordinate
  fin_cases coordinate <;>
    simp [phaseHamiltonianVector, rotatingKeplerDifferential,
      rotatingKeplerVectorField, coordinateVector]; ring

/-- Convert eccentric anomaly to mean anomaly at the anchor eccentricity. -/
noncomputable def delaunayAnchorMeanFromEccentricAngles
    (angles : ℝ × ℝ) : ℝ × ℝ :=
  (eccentricMeanAnomaly (1 / 2) angles.1, angles.2)

/-- The angle slice of the full anchor chart. -/
noncomputable def delaunayAnchorEccentricAngleChart
    (angles : ℝ × ℝ) : PhaseSpace :=
  delaunayAnchorChart (delaunayAnchorAction, angles)

/--
@isnad1 id=hasfderi.0h0v.s8.c90bc85f81f4 from=translated src=- shape=3fc31608 vocab=c4cc3e28
-/
theorem hasFDerivAt_delaunayAnchorMeanFromEccentricAngles :
    HasFDerivAt delaunayAnchorMeanFromEccentricAngles
      (((ContinuousLinearMap.toSpanSingleton ℝ (1 / 2 : ℝ)).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ))
      delaunayAnchorMeanAngles := by
  have hmeanScalar : HasDerivAt (eccentricMeanAnomaly (1 / 2))
      (1 / 2 : ℝ) 0 := by
    convert hasDerivAt_eccentricMeanAnomaly (1 / 2) 0 using 1
    norm_num
  have hfst : HasFDerivAt (fun angles : ℝ × ℝ ↦ angles.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) delaunayAnchorMeanAngles :=
    hasFDerivAt_fst
  have hmean := hmeanScalar.hasFDerivAt.comp
    delaunayAnchorMeanAngles hfst
  exact hmean.prodMk hasFDerivAt_snd

/--
@isnad1 id=injectiv.0h0v.s9.476271bd8d2a from=translated src=- shape=f8b4ffe5 vocab=e2cacfad
-/
theorem injective_fderiv_delaunayAnchorMeanFromEccentricAngles :
    Function.Injective
      (fderiv ℝ delaunayAnchorMeanFromEccentricAngles
        delaunayAnchorMeanAngles) := by
  rw [hasFDerivAt_delaunayAnchorMeanFromEccentricAngles.fderiv]
  intro first second hequal
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hequal
    simpa using hfirst
  · have hsecond := congrArg Prod.snd hequal
    simpa using hsecond

end LeanPool.PoincareThreeBody
