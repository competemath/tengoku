import Tengoku.AlbertFrameTripleInvariants.AlbertLean.WitnessData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- Nine raw joint moments in standard diagonal slot 1.-/
theorem witnessSameJoint01 (j l : Fin 3) :
    traceForm (projector theta1E 1)
      (structuredProduct (projector theta1F j) (projector theta1K l)) =
    traceForm (projector thetaME 1)
      (structuredProduct (projector thetaMF j) (projector thetaMK l)) := by
  rw [thetaME_eq_theta1E_fast,
    traceForm_projector_theta1E_left, traceForm_projector_theta1E_left]
  change structuredProduct (projector theta1F j) (projector theta1K l) (1 : Fin 27) =
    structuredProduct (projector thetaMF j) (projector thetaMK l) (1 : Fin 27)
  rw [structuredProduct_eq_productForm, structuredProduct_eq_productForm]
  fin_cases j <;> fin_cases l <;>
    simp only [projector, theta1F_square, theta1K_square, thetaMF_square, thetaMK_square]
  all_goals
    norm_num [productForm, Theta1FSquare, Theta1KSquare, ThetaMFSquare, ThetaMKSquare,
      theta1F, theta1K, thetaMF, thetaMK, one, v, q]

end AlbertLean
