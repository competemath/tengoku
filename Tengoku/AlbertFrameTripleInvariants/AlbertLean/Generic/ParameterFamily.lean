import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.WitnessChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A reciprocal one-parameter family of lawful residual charts

The accepted witnesses are the parameters `1` and `witnessScale` in one
normalized family.  The retained moment matrix is fixed, while the normalized
vector determinant is an arbitrary nonzero rational `t`; the covector
determinant is consequently `witnessScale / t`.  Thus the family varies the
residual base through the symmetric root sum `t + witnessScale / t`, and root
exchange is the reciprocal involution `t ↦ witnessScale / t`.

This is an explicit chart family.  It makes no global chart-coverage,
quotient, descent, or detector-separation claim.
-/

noncomputable section

namespace AlbertLean.Generic.ParameterFamily

open Matrix
open AlbertLean
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.WitnessChart
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction

/-- The accepted residual moment, held fixed throughout the family.-/
def parameterMoment : Matrix (Fin 4) (Fin 4) ℚ :=
  moment (residualPairOfChart witnessChart1)

/-- The determinant of the fixed moment is the accepted nontrivial root.-/
theorem parameterMoment_det : Matrix.det parameterMoment = witnessScale := by
  rw [parameterMoment, moment, Matrix.det_mul]
  change deltaStar (residualPairOfChart witnessChart1) *
      delta (residualPairOfChart witnessChart1) = witnessScale
  rw [witnessChart1_deltaStar, witnessChart1_delta]
  ring

theorem witnessScale_ne_zero : witnessScale ≠ 0 := by
  norm_num [witnessScale]

/-- The normalized section with root parameter `t` and the accepted fixed
moment.-/
def parameterSection (t : ℚ) (ht : t ≠ 0) :
    AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection ℚ where
  M := parameterMoment
  Delta := t
  Delta_ne_zero := ht
  detM_ne_zero := by
    rw [parameterMoment_det]
    exact witnessScale_ne_zero

/-- The residual matrix pair represented by the normalized section at `t`.
Its vector matrix is `diag(1,1,1,t)` and its covector matrix is the fixed
moment times the inverse of that diagonal matrix.-/
def parameterResidualPair (t : ℚ) (ht : t ≠ 0) : ResidualPair ℚ :=
  residualPairOfSection (parameterSection t ht)

/-- Reinsert the parameterized residual pair while retaining all non-residual
coordinates of the first accepted chart.-/
def parameterChart (t : ℚ) (ht : t ≠ 0) : ExplicitFrameChart ℚ :=
  chartWithResidualPair witnessChart1 (parameterResidualPair t ht)

/-- The ordered public triple carried by the parameterized chart.-/
def parameterTriple (t : ℚ) (ht : t ≠ 0) : WitnessTriple :=
  chartWitnessTriple (parameterChart t ht)

@[simp] theorem parameterResidualPair_moment (t : ℚ) (ht : t ≠ 0) :
    moment (parameterResidualPair t ht) = parameterMoment := by
  simp [parameterResidualPair, parameterSection]

@[simp] theorem parameterResidualPair_delta (t : ℚ) (ht : t ≠ 0) :
    delta (parameterResidualPair t ht) = t := by
  simp [parameterResidualPair, parameterSection]

@[simp] theorem parameterResidualPair_deltaStar (t : ℚ) (ht : t ≠ 0) :
    deltaStar (parameterResidualPair t ht) = witnessScale / t := by
  simp [parameterResidualPair, parameterSection,
    AlbertLean.Residual.NormalizedRootSwap.DeltaStar,
    parameterMoment_det]

@[simp] theorem parameterResidualPair_X (t : ℚ) (ht : t ≠ 0) :
    (parameterResidualPair t ht).X =
      AlbertLean.Residual.NormalizedOrbitSection.X0 t := rfl

/-- The covector matrix has the promised inverse-diagonal normal form.-/
theorem parameterResidualPair_A (t : ℚ) (ht : t ≠ 0) :
    (parameterResidualPair t ht).A = parameterMoment *
      AlbertLean.Residual.NormalizedOrbitSection.X0Inv t := by
  have hAX : (parameterResidualPair t ht).A *
      AlbertLean.Residual.NormalizedOrbitSection.X0 t = parameterMoment := by
    rw [← parameterResidualPair_X]
    exact parameterResidualPair_moment t ht
  calc
    (parameterResidualPair t ht).A =
        (parameterResidualPair t ht).A * 1 := (Matrix.mul_one _).symm
    _ = (parameterResidualPair t ht).A *
        (AlbertLean.Residual.NormalizedOrbitSection.X0 t *
          AlbertLean.Residual.NormalizedOrbitSection.X0Inv t) := by
      rw [AlbertLean.Residual.NormalizedOrbitSection.X0_mul_X0Inv t ht]
    _ = ((parameterResidualPair t ht).A *
          AlbertLean.Residual.NormalizedOrbitSection.X0 t) *
        AlbertLean.Residual.NormalizedOrbitSection.X0Inv t := by
      rw [Matrix.mul_assoc]
    _ = parameterMoment *
        AlbertLean.Residual.NormalizedOrbitSection.X0Inv t := by rw [hAX]

/-- Entrywise form of `A(t) X₀(t) = M`, useful for downstream symbolic
ledger calculations without exposing a matrix-inverse expansion.-/
theorem parameterResidualPair_A_mul_diagonal (t : ℚ) (ht : t ≠ 0)
    (i j : Fin 4) :
    (parameterResidualPair t ht).A i j * ![1, 1, 1, t] j =
      parameterMoment i j := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M i j)
    (parameterResidualPair_moment t ht)
  rw [moment, parameterResidualPair_X] at h
  fin_cases j <;>
    simpa [AlbertLean.Residual.NormalizedOrbitSection.X0, Matrix.mul_apply,
      Fin.sum_univ_succ] using h

@[simp] theorem parameterResidualPair_A_zero (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 0 = parameterMoment i 0 := by
  simpa using parameterResidualPair_A_mul_diagonal t ht i 0

@[simp] theorem parameterResidualPair_A_one (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 1 = parameterMoment i 1 := by
  simpa using parameterResidualPair_A_mul_diagonal t ht i 1

@[simp] theorem parameterResidualPair_A_two (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 2 = parameterMoment i 2 := by
  simpa using parameterResidualPair_A_mul_diagonal t ht i 2

@[simp] theorem parameterResidualPair_A_three (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 3 = parameterMoment i 3 / t := by
  have h := parameterResidualPair_A_mul_diagonal t ht i 3
  change (parameterResidualPair t ht).A i 3 * t = parameterMoment i 3 at h
  exact (eq_div_iff ht).2 h

theorem parameterResidualPair_open (t : ℚ) (ht : t ≠ 0) :
    ResidualOpen (parameterResidualPair t ht) := by
  exact residualPairOfSection_open (parameterSection t ht)

@[simp] theorem parameterResidualPair_baseRootSum (t : ℚ) (ht : t ≠ 0) :
    baseRootSum (parameterResidualPair t ht) = t + witnessScale / t := by
  simp [baseRootSum]

@[simp] theorem parameterChart_residualPair (t : ℚ) (ht : t ≠ 0) :
    residualPairOfChart (parameterChart t ht) = parameterResidualPair t ht := by
  simp [parameterChart]

@[simp] theorem parameterChart_equationValues (t : ℚ) (ht : t ≠ 0) :
    explicitFrameEquationValues (parameterChart t ht) =
      explicitFrameEquationValues witnessChart1 := by
  apply explicitFrameEquationValues_chartWithResidualPair_of_moment_eq
  rw [parameterResidualPair_moment]
  rfl

/-- Every nonzero rational parameter produces a lawful ordered public frame
triple; this follows from fixed moment, without expanding source coordinates.-/
theorem parameterTriple_lawful (t : ℚ) (ht : t ≠ 0) :
    LawfulFrameTriple (parameterTriple t ht) := by
  rw [parameterTriple, ← equationsVanish_iff_lawfulFrameTriple,
    parameterChart_equationValues]
  exact witnessChart1_equations

theorem reciprocalParameter_ne_zero (t : ℚ) (ht : t ≠ 0) :
    witnessScale / t ≠ 0 :=
  div_ne_zero witnessScale_ne_zero ht

/-- Reciprocal parameters have the same moment and symmetric root sum.-/
theorem parameterResidualPair_reciprocal_sameBase (t : ℚ) (ht : t ≠ 0) :
    sameResidualBase (parameterResidualPair t ht)
      (parameterResidualPair (witnessScale / t)
        (reciprocalParameter_ne_zero t ht)) := by
  constructor
  · simp [baseMoment]
  · simp only [parameterResidualPair_baseRootSum]
    field_simp [ht, witnessScale_ne_zero] <;> ring

/-- On this normalized family, the genuine section root swap is exactly the
reciprocal parameter involution.-/
theorem parameterResidualPair_rootSwapped (t : ℚ) (ht : t ≠ 0) :
    rootSwappedRepresentative (parameterResidualPair t ht)
        (parameterResidualPair_open t ht) =
      parameterResidualPair (witnessScale / t)
        (reciprocalParameter_ne_zero t ht) := by
  let s := parameterSection t ht
  have hs : AlbertLean.Residual.NormalizedRootSwap.rootSwap s =
      parameterSection (witnessScale / t)
        (reciprocalParameter_ne_zero t ht) := by
    apply AlbertLean.Residual.NormalizedRootSwap.NormalizedResidualSection.ext
    · rfl
    · simp [s, parameterSection,
        AlbertLean.Residual.NormalizedRootSwap.DeltaStar,
        parameterMoment_det]
  unfold rootSwappedRepresentative parameterResidualPair
  rw [section_residual_roundtrip]
  exact congrArg residualPairOfSection hs

/-- Any normalized residual pair with the fixed moment and displayed vector
matrix is the corresponding member of the parameter family.-/
theorem parameterResidualPair_eq_of_moment_X (t : ℚ) (ht : t ≠ 0)
    (P : ResidualPair ℚ) (hM : moment P = parameterMoment)
    (hX : P.X = AlbertLean.Residual.NormalizedOrbitSection.X0 t) :
    parameterResidualPair t ht = P := by
  apply ResidualPair.ext
  · rw [parameterResidualPair_A]
    calc
      parameterMoment * AlbertLean.Residual.NormalizedOrbitSection.X0Inv t =
          moment P * AlbertLean.Residual.NormalizedOrbitSection.X0Inv t := by
        rw [hM]
      _ = (P.A * P.X) *
          AlbertLean.Residual.NormalizedOrbitSection.X0Inv t := rfl
      _ = P.A * (P.X *
          AlbertLean.Residual.NormalizedOrbitSection.X0Inv t) := by
        rw [Matrix.mul_assoc]
      _ = P.A * 1 := by
        rw [hX,
          AlbertLean.Residual.NormalizedOrbitSection.X0_mul_X0Inv t ht]
      _ = P.A := Matrix.mul_one _
  · exact (parameterResidualPair_X t ht).trans hX.symm

theorem parameterResidualPair_one :
    parameterResidualPair 1 one_ne_zero = residualPairOfChart witnessChart1 := by
  apply parameterResidualPair_eq_of_moment_X
  · rfl
  · rw [witnessChart1_X]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AlbertLean.Residual.NormalizedOrbitSection.X0, Matrix.one_apply]

theorem parameterResidualPair_witnessScale :
    parameterResidualPair witnessScale witnessScale_ne_zero =
      residualPairOfChart witnessChartM := by
  apply parameterResidualPair_eq_of_moment_X
  · exact witnessCharts_moment_eq
  · simpa [AlbertLean.Residual.NormalizedOrbitSection.X0] using witnessChartM_X

theorem parameterChart_one : parameterChart 1 one_ne_zero = witnessChart1 := by
  rw [parameterChart, parameterResidualPair_one, chartWithResidualPair_self]

theorem parameterChart_witnessScale :
    parameterChart witnessScale witnessScale_ne_zero = witnessChartM := by
  rw [parameterChart, parameterResidualPair_witnessScale]
  exact witnessChartM_eq_reinsert.symm

theorem parameterTriple_one :
    parameterTriple 1 one_ne_zero = chartWitnessTriple witnessChart1 := by
  rw [parameterTriple, parameterChart_one]

theorem parameterTriple_witnessScale :
    parameterTriple witnessScale witnessScale_ne_zero =
      chartWitnessTriple witnessChartM := by
  rw [parameterTriple, parameterChart_witnessScale]

end AlbertLean.Generic.ParameterFamily
