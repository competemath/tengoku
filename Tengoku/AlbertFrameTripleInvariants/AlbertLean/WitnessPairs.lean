import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem witnessSameP : (ledger witnessTheta1).P = (ledger witnessThetaM).P := by
  funext i j
  change traceForm (projector theta1E i) (projector theta1F j) =
    traceForm (projector thetaME i) (projector thetaMF j)
  rw [thetaME_eq_theta1E_fast,
    traceForm_projector_theta1E_left, traceForm_projector_theta1E_left]
  fin_cases i <;> fin_cases j <;>
    simp only [projector, theta1F_square, thetaMF_square]
  all_goals
    norm_num [Theta1FSquare, ThetaMFSquare, theta1F, thetaMF, one, v, q]

theorem witnessSameQ : (ledger witnessTheta1).Q = (ledger witnessThetaM).Q := by
  funext j l
  change traceForm (projector theta1F j) (projector theta1K l) =
    traceForm (projector thetaMF j) (projector thetaMK l)
  fin_cases j <;> fin_cases l <;>
    simp only [projector, theta1F_square, thetaMF_square, theta1K_square, thetaMK_square]
  all_goals
    norm_num [traceForm_eq_fast, traceLinearForm, spurPairForm,
      Theta1FSquare, ThetaMFSquare, Theta1KSquare, ThetaMKSquare,
      theta1F, thetaMF, theta1K, thetaMK, one, v, q]

theorem witnessSameR : (ledger witnessTheta1).R = (ledger witnessThetaM).R := by
  funext l i
  change traceForm (projector theta1K l) (projector theta1E i) =
    traceForm (projector thetaMK l) (projector thetaME i)
  rw [thetaME_eq_theta1E_fast,
    traceForm_projector_theta1E_right, traceForm_projector_theta1E_right]
  fin_cases l <;> fin_cases i <;>
    simp only [projector, theta1K_square, thetaMK_square]
  all_goals
    norm_num [Theta1KSquare, ThetaMKSquare, theta1K, thetaMK, one, v, q]

end AlbertLean
