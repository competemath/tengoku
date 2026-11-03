import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceChartDiagonalReadback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms moment_parameters` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms openParameters` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms insert_openParameters_eq_normalized` (it only prints; the queue checks the axioms of every declaration). -/

/-! Literal reconstruction of the normalized twenty-parameter chart from an
actual lawful explicit chart on the stated principal open.  This is a pointwise
section theorem, not dominance or invariant-field generation. -/

noncomputable section
namespace AlbertLean.Generic.SourceNormalizedChartReadback

open Matrix
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.NormalizedOrbitSection
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.GenericNormalizedFrameChart
open AlbertLean.Generic.SourceChartDiagonalReadback

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem moment_parameters (q : ExplicitFrameChart K)
    (hr : q.r1 = 1)
    (hq : EquationsVanish (explicitFrameEquationValues q))
    (hpA : q.diagA 1 - q.diagA 2 ≠ 0)
    (hpB : q.diagB 1 - q.diagB 2 ≠ 0) :
    GenericNormalizedFrameChart.moment (parameters q) = matrixM q := by
  have hd := omitted_diagonal q hq
  have hs := actual_diagonal_systems q hr hq
  have hA := solve_diagonal_pair
    (q.diagA 1) (q.diagA 2) (spurSumA (parameters q))
    (normWeightedA (parameters q)) (matrixM q 0 0) (matrixM q 2 2)
    hpA hs.1 hs.2.1
  have hB := solve_diagonal_pair
    (q.diagB 1) (q.diagB 2) (spurSumB (parameters q))
    (normWeightedB (parameters q)) (matrixM q 1 1) (matrixM q 3 3)
    hpB hs.2.2.1 hs.2.2.2
  have hm00 : m00 (parameters q) = matrixM q 0 0 := by
    rw [m00, pivotA, hd.1]
    exact hA.1
  have hm22 : m22 (parameters q) = matrixM q 2 2 := by
    rw [m22, hm00]
    linear_combination -hs.1
  have hm11 : m11 (parameters q) = matrixM q 1 1 := by
    rw [m11, pivotB, hd.2]
    exact hB.1
  have hm33 : m33 (parameters q) = matrixM q 3 3 := by
    rw [m33, hm11]
    linear_combination -hs.2.2.1
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      simp [GenericNormalizedFrameChart.moment, hm00, hm11, hm22, hm33]
  · simp [GenericNormalizedFrameChart.moment, hij, parameters]

def openParameters (q : ExplicitFrameChart K)
    (hq : EquationsVanish (explicitFrameEquationValues q))
    (hpA : q.diagA 1 - q.diagA 2 ≠ 0)
    (hpB : q.diagB 1 - q.diagB 2 ≠ 0)
    (hDelta : Matrix.det (residualPairOfChart q).X ≠ 0)
    (hMoment : Matrix.det (matrixM q) ≠ 0)
    (hbranch : Matrix.det (residualPairOfChart q).X ^ 2 ≠
      Matrix.det (matrixM q))
    (hr : q.r1 = 1) : OpenParameters K where
  toParameters := parameters q
  pivotA_ne := by
    have hd := (omitted_diagonal q hq).1
    rw [pivotA, hd]
    exact hpA
  pivotB_ne := by
    have hd := (omitted_diagonal q hq).2
    rw [pivotB, hd]
    exact hpB
  Delta_ne := hDelta
  detMoment_ne := by
    rw [moment_parameters q hr hq hpA hpB]
    exact hMoment
  branch_ne := by
    rw [moment_parameters q hr hq hpA hpB]
    exact hbranch

private theorem matrixM_eq_residual_moment (q : ExplicitFrameChart K) :
    matrixM q = AlbertLean.Residual.SL4PairAction.moment
      (residualPairOfChart q) := by
  simpa [matrixM, residualPairOfChart,
    AlbertLean.Residual.SL4PairAction.moment] using
    (AlbertLean.Residual.ResidualMatrices.momentMatrix_eq_AMatrix_mul_XMatrix
      q.s1 q.s2 q.c1 q.c2)

private theorem chartWithResidualPair_self (x : ExplicitFrameChart K) :
    chartWithResidualPair x (residualPairOfChart x) = x := by
  apply ExplicitFrameChart.ext <;> try rfl

/-- The accepted determinant-one normalizer sends the actual chart to the
literal normalized insertion of its twenty read coordinates.-/
theorem insert_openParameters_eq_normalized (q : ExplicitFrameChart K)
    (hr : q.r1 = 1) (hk : IsKappaLift q)
    (hq : EquationsVanish (explicitFrameEquationValues q))
    (hpA : q.diagA 1 - q.diagA 2 ≠ 0)
    (hpB : q.diagB 1 - q.diagB 2 ≠ 0)
    (hDelta : Matrix.det (residualPairOfChart q).X ≠ 0)
    (hMoment : Matrix.det (matrixM q) ≠ 0)
    (hbranch : Matrix.det (residualPairOfChart q).X ^ 2 ≠
      Matrix.det (matrixM q)) :
    let p := openParameters q hq hpA hpB hDelta hMoment hbranch hr
    let G := normalizingDetOneMatrix (residualPairOfChart q) hDelta
    GenericNormalizedFrameChart.insert p = actChart G q := by
  dsimp only
  let p := openParameters q hq hpA hpB hDelta hMoment hbranch hr
  let P := residualPairOfChart q
  let G := normalizingDetOneMatrix P hDelta
  have hMP : GenericNormalizedFrameChart.moment p.toParameters =
      AlbertLean.Residual.SL4PairAction.moment P := by
    rw [show p.toParameters = parameters q by rfl,
      moment_parameters q hr hq hpA hpB,
      matrixM_eq_residual_moment]
  have hresInsert : residualPairOfChart
      (GenericNormalizedFrameChart.insert p) = normalizedPair P := by
    rw [insert_residualPair]
    apply ResidualPair.ext
    · change GenericNormalizedFrameChart.moment p.toParameters *
        X0Inv (delta P) =
        AlbertLean.Residual.SL4PairAction.moment P * X0Inv (delta P)
      rw [hMP]
    · rfl
  have hresAct : residualPairOfChart (actChart G q) = normalizedPair P := by
    calc
      residualPairOfChart (actChart G q) = act G P :=
        residualPairOfChart_actChart G q
      _ = normalizedPair P := act_normalizingDetOneMatrix P hDelta
  have hres : residualPairOfChart (GenericNormalizedFrameChart.insert p) =
      residualPairOfChart (actChart G q) := hresInsert.trans hresAct.symm
  have hkappa : q.kappa = q.z2 - q.r2 * q.z1 := by
    have H := hk
    simp only [IsKappaLift, orientation, hr, one_mul] at H
    linear_combination -H
  have hactRecover :
      chartWithResidualPair q (residualPairOfChart (actChart G q)) =
        actChart G q := by
    change chartWithResidualPair (actChart G q)
      (residualPairOfChart (actChart G q)) = actChart G q
    exact chartWithResidualPair_self _
  have hinsertRecover :
      chartWithResidualPair q
        (residualPairOfChart (GenericNormalizedFrameChart.insert p)) =
          GenericNormalizedFrameChart.insert p := by
    calc
      chartWithResidualPair q
          (residualPairOfChart (GenericNormalizedFrameChart.insert p)) =
          chartWithResidualPair (GenericNormalizedFrameChart.insert p)
            (residualPairOfChart (GenericNormalizedFrameChart.insert p)) := by
        apply ExplicitFrameChart.ext
        · funext i
          change q.diagA i = (GenericNormalizedFrameChart.insert p).diagA i
          fin_cases i
          · rfl
          · rfl
          · change q.diagA 2 = dA2 (parameters q)
            exact (omitted_diagonal q hq).1.symm
        · funext i
          change q.diagB i = (GenericNormalizedFrameChart.insert p).diagB i
          fin_cases i
          · rfl
          · rfl
          · change q.diagB 2 = dB2 (parameters q)
            exact (omitted_diagonal q hq).2.symm
        · change q.r1 = 1
          exact hr
        · rfl
        · rfl
        · rfl
        · change q.kappa = q.z2 - q.z1 * q.r2
          rw [hkappa]
          ring
        · rfl
        · rfl
        · rfl
        · rfl
      _ = GenericNormalizedFrameChart.insert p := chartWithResidualPair_self _
  calc
    GenericNormalizedFrameChart.insert p = chartWithResidualPair q
        (residualPairOfChart (GenericNormalizedFrameChart.insert p)) :=
      hinsertRecover.symm
    _ = chartWithResidualPair q (residualPairOfChart (actChart G q)) := by
      rw [hres]
    _ = actChart G q := hactRecover

end AlbertLean.Generic.SourceNormalizedChartReadback
