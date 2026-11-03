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

/-- The determinant of the fixed moment is the accepted nontrivial root.
@isnad1 id=eq.0h0v.s4.17ccc9b92dcf from=translated src=- shape=fdab990c vocab=19e8027b
-/
theorem parameterMoment_det : Matrix.det parameterMoment = witnessScale := by
  rw [parameterMoment, moment, Matrix.det_mul]
  change deltaStar (residualPairOfChart witnessChart1) *
      delta (residualPairOfChart witnessChart1) = witnessScale
  rw [witnessChart1_deltaStar, witnessChart1_delta]
  ring

/--
@isnad1 id=ne.0h0v.s3.316a2c019bc6 from=translated src=- shape=ffdda526 vocab=8331fb2c
-/
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

/--
@isnad1 id=eq.1h1v.s4.c5d702b65bb8 from=translated src=- shape=8192d51d vocab=032dc85e
-/
@[simp] theorem parameterResidualPair_moment (t : ℚ) (ht : t ≠ 0) :
    moment (parameterResidualPair t ht) = parameterMoment := by
  simp [parameterResidualPair, parameterSection]

/--
@isnad1 id=eq.1h1v.s4.3ddb2f865d45 from=translated src=- shape=ae92ed67 vocab=058d6d74
-/
@[simp] theorem parameterResidualPair_delta (t : ℚ) (ht : t ≠ 0) :
    delta (parameterResidualPair t ht) = t := by
  simp [parameterResidualPair, parameterSection]

/--
@isnad1 id=eq.1h1v.s4.bae4d93970bf from=translated src=- shape=4fa19d47 vocab=31b89ba9
-/
@[simp] theorem parameterResidualPair_deltaStar (t : ℚ) (ht : t ≠ 0) :
    deltaStar (parameterResidualPair t ht) = witnessScale / t := by
  simp [parameterResidualPair, parameterSection,
    AlbertLean.Residual.NormalizedRootSwap.DeltaStar,
    parameterMoment_det]

/--
@isnad1 id=eq.1h1v.s4.5b99b570228d from=translated src=- shape=a12bb286 vocab=9c142bae
-/
@[simp] theorem parameterResidualPair_X (t : ℚ) (ht : t ≠ 0) :
    (parameterResidualPair t ht).X =
      AlbertLean.Residual.NormalizedOrbitSection.X0 t := rfl

/-- The covector matrix has the promised inverse-diagonal normal form.
@isnad1 id=eq.1h1v.s6.730d95248ec1 from=translated src=- shape=9def9f0b vocab=d86ab1e1
-/
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
ledger calculations without exposing a matrix-inverse expansion.
@isnad1 id=eq.1h3v.s6.18b17613f33e from=translated src=- shape=f27c566a vocab=574de1df
-/
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

/--
@isnad1 id=eq.1h2v.s5.35f9c896b5bc from=translated src=- shape=47d99284 vocab=d834f854
-/
@[simp] theorem parameterResidualPair_A_zero (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 0 = parameterMoment i 0 := by
  simpa using parameterResidualPair_A_mul_diagonal t ht i 0

/--
@isnad1 id=eq.1h2v.s5.c28be0bab90c from=translated src=- shape=47d99284 vocab=d834f854
-/
@[simp] theorem parameterResidualPair_A_one (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 1 = parameterMoment i 1 := by
  simpa using parameterResidualPair_A_mul_diagonal t ht i 1

/--
@isnad1 id=eq.1h2v.s5.fad308cc91fe from=translated src=- shape=47d99284 vocab=d834f854
-/
@[simp] theorem parameterResidualPair_A_two (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 2 = parameterMoment i 2 := by
  simpa using parameterResidualPair_A_mul_diagonal t ht i 2

/--
@isnad1 id=eq.1h2v.s6.78f50e5c69a0 from=translated src=- shape=9a8700e0 vocab=2ad6b214
-/
@[simp] theorem parameterResidualPair_A_three (t : ℚ) (ht : t ≠ 0)
    (i : Fin 4) :
    (parameterResidualPair t ht).A i 3 = parameterMoment i 3 / t := by
  have h := parameterResidualPair_A_mul_diagonal t ht i 3
  change (parameterResidualPair t ht).A i 3 * t = parameterMoment i 3 at h
  exact (eq_div_iff ht).2 h

/--
@isnad1 id=residual.1h1v.s4.6d64fc6240f9 from=translated src=- shape=4386287b vocab=9e681ad6
-/
theorem parameterResidualPair_open (t : ℚ) (ht : t ≠ 0) :
    ResidualOpen (parameterResidualPair t ht) := by
  exact residualPairOfSection_open (parameterSection t ht)

/--
@isnad1 id=eq.1h1v.s5.f86b3aedd667 from=translated src=- shape=21a25b30 vocab=df407f7b
-/
@[simp] theorem parameterResidualPair_baseRootSum (t : ℚ) (ht : t ≠ 0) :
    baseRootSum (parameterResidualPair t ht) = t + witnessScale / t := by
  simp [baseRootSum]

/--
@isnad1 id=eq.1h1v.s4.c27d37a5dbd2 from=translated src=- shape=377673ea vocab=5c87011e
-/
@[simp] theorem parameterChart_residualPair (t : ℚ) (ht : t ≠ 0) :
    residualPairOfChart (parameterChart t ht) = parameterResidualPair t ht := by
  simp [parameterChart]

/--
@isnad1 id=eq.1h1v.s4.573d741d6a18 from=translated src=- shape=9bcedb3d vocab=983147a4
-/
@[simp] theorem parameterChart_equationValues (t : ℚ) (ht : t ≠ 0) :
    explicitFrameEquationValues (parameterChart t ht) =
      explicitFrameEquationValues witnessChart1 := by
  apply explicitFrameEquationValues_chartWithResidualPair_of_moment_eq
  rw [parameterResidualPair_moment]
  rfl

/-- Every nonzero rational parameter produces a lawful ordered public frame
triple; this follows from fixed moment, without expanding source coordinates.
@isnad1 id=lawfulfr.1h1v.s3.5f1049d1e7c1 from=translated src=- shape=da80b8de vocab=03a7e234
-/
theorem parameterTriple_lawful (t : ℚ) (ht : t ≠ 0) :
    LawfulFrameTriple (parameterTriple t ht) := by
  rw [parameterTriple, ← equationsVanish_iff_lawfulFrameTriple,
    parameterChart_equationValues]
  exact witnessChart1_equations

/--
@isnad1 id=ne.1h1v.s4.827ba507b5dd from=translated src=- shape=e4446b89 vocab=2b9f25c2
-/
theorem reciprocalParameter_ne_zero (t : ℚ) (ht : t ≠ 0) :
    witnessScale / t ≠ 0 :=
  div_ne_zero witnessScale_ne_zero ht

/-- Reciprocal parameters have the same moment and symmetric root sum.
@isnad1 id=sameresi.1h1v.s4.22f8c197964c from=translated src=- shape=e6ef3c58 vocab=9d6e7f77
-/
theorem parameterResidualPair_reciprocal_sameBase (t : ℚ) (ht : t ≠ 0) :
    sameResidualBase (parameterResidualPair t ht)
      (parameterResidualPair (witnessScale / t)
        (reciprocalParameter_ne_zero t ht)) := by
  constructor
  · simp [baseMoment]
  · simp only [parameterResidualPair_baseRootSum]
    field_simp [ht, witnessScale_ne_zero] <;> ring

/-- On this normalized family, the genuine section root swap is exactly the
reciprocal parameter involution.
@isnad1 id=eq.1h1v.s5.5cc4e4becb76 from=translated src=- shape=3664a895 vocab=3413acc1
-/
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
matrix is the corresponding member of the parameter family.
@isnad1 id=eq.3h2v.s5.eac7782dd42e from=translated src=- shape=d19c71b8 vocab=1b9b472b
-/
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

/--
@isnad1 id=eq.0h0v.s4.9aa0eadb84b6 from=translated src=- shape=9b9f70e7 vocab=54342f82
-/
theorem parameterResidualPair_one :
    parameterResidualPair 1 one_ne_zero = residualPairOfChart witnessChart1 := by
  apply parameterResidualPair_eq_of_moment_X
  · rfl
  · rw [witnessChart1_X]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AlbertLean.Residual.NormalizedOrbitSection.X0, Matrix.one_apply]

/--
@isnad1 id=eq.0h0v.s3.8e05613560a1 from=translated src=- shape=eb166657 vocab=12d60a3f
-/
theorem parameterResidualPair_witnessScale :
    parameterResidualPair witnessScale witnessScale_ne_zero =
      residualPairOfChart witnessChartM := by
  apply parameterResidualPair_eq_of_moment_X
  · exact witnessCharts_moment_eq
  · simpa [AlbertLean.Residual.NormalizedOrbitSection.X0] using witnessChartM_X

/--
@isnad1 id=eq.0h0v.s3.97a1aba02da6 from=translated src=- shape=2a0c1b02 vocab=fb747d44
-/
theorem parameterChart_one : parameterChart 1 one_ne_zero = witnessChart1 := by
  rw [parameterChart, parameterResidualPair_one, chartWithResidualPair_self]

/--
@isnad1 id=eq.0h0v.s3.efc86616460c from=translated src=- shape=18f21e71 vocab=1bbd6c55
-/
theorem parameterChart_witnessScale :
    parameterChart witnessScale witnessScale_ne_zero = witnessChartM := by
  rw [parameterChart, parameterResidualPair_witnessScale]
  exact witnessChartM_eq_reinsert.symm

/--
@isnad1 id=eq.0h0v.s3.f5965ffeec46 from=translated src=- shape=a0ccde3f vocab=fa0ece7d
-/
theorem parameterTriple_one :
    parameterTriple 1 one_ne_zero = chartWitnessTriple witnessChart1 := by
  rw [parameterTriple, parameterChart_one]

/--
@isnad1 id=eq.0h0v.s2.3376bc62d2ae from=translated src=- shape=93dc8cbf vocab=f3ab5af8
-/
theorem parameterTriple_witnessScale :
    parameterTriple witnessScale witnessScale_ne_zero =
      chartWitnessTriple witnessChartM := by
  rw [parameterTriple, parameterChart_witnessScale]

end AlbertLean.Generic.ParameterFamily
