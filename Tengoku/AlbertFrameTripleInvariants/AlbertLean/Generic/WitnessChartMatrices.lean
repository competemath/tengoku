import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.WitnessChartData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Literal vector-column matrices of the accepted chart witnesses

Source-record readers are removed by a definitional change before any
finite arithmetic. The two vector matrices are checked separately from
covector determinants and moments to keep each compilation small.
-/

noncomputable section

namespace AlbertLean.Generic.WitnessChart

open AlbertLean
open AlbertLean.Generic.ChartBridge

/-- The first vector-column matrix is literally the identity.
@isnad1 id=eq.0h0v.s5.18f00e65a024 from=translated src=- shape=3a0b6f1e vocab=0c5a385f
-/
theorem witnessChart1_X : (residualPairOfChart witnessChart1).X = 1 := by
  change
    (fun i j : Fin 4 =>
      ![(![q 1 1, 0, 0, 0] : Fin 4 → ℚ) i,
        (![0, q 1 1, 0, 0] : Fin 4 → ℚ) i,
        (![0, 0, q 1 1, 0] : Fin 4 → ℚ) i,
        (![0, 0, 0, q 1 1] : Fin 4 → ℚ) i] j) =
      (1 : Matrix (Fin 4) (Fin 4) ℚ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q, Matrix.one_apply]

/-- The second vector-column matrix is the displayed diagonal representative.
@isnad1 id=eq.0h0v.s6.966e043a80de from=translated src=- shape=16687ae1 vocab=3d665e24
-/
theorem witnessChartM_X :
    (residualPairOfChart witnessChartM).X =
      Matrix.diagonal ![1, 1, 1, witnessScale] := by
  change
    (fun i j : Fin 4 =>
      ![(![q 1 1, 0, 0, 0] : Fin 4 → ℚ) i,
        (![0, q 1 1, 0, 0] : Fin 4 → ℚ) i,
        (![0, 0, q 1 1, 0] : Fin 4 → ℚ) i,
        (![0, 0, 0, q 410231 5832] : Fin 4 → ℚ) i] j) =
      Matrix.diagonal ![1, 1, 1, witnessScale]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q, Matrix.diagonal, witnessScale]

end AlbertLean.Generic.WitnessChart
