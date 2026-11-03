import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/--
@isnad1 id=eq.0h0v.s4.b51645782e67 from=translated src=- shape=c6b96a7a vocab=73138a68
-/
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

/--
@isnad1 id=eq.0h0v.s4.53c9f20af006 from=translated src=- shape=c6b96a7a vocab=1e9141d3
-/
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

/--
@isnad1 id=eq.0h0v.s4.38141c4bf330 from=translated src=- shape=c6b96a7a vocab=1bf7e1b1
-/
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
