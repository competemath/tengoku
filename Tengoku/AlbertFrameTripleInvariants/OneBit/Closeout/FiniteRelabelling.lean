import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Solution
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The nine idempotents of a configuration and their pair traces as numbers

`family X r i` is idempotent i of frame r of a configuration X, `pair X r s i j` the
trace form of two of them. `marginal` lists the three pair-trace matrices of the first
configuration (P between frames 0 and 1, Q between 1 and 2, R between 2 and 0; the reverse
order is the transpose), and `pair_eq_marginal` checks by exact rational arithmetic that
these are the values of `pair`. The matrices are the numerical input to `MarginalRigidity`.
-/

namespace OneBit.Closeout
open AlbertLean
open scoped BigOperators

/-- The nine literal rational projectors, with their original labels.-/
def family (X : WitnessTriple) (r i : Fin 3) : Coord := projector (AlbertLean.encoder X r) i

def pair (X : WitnessTriple) (r s i j : Fin 3) : ℚ :=
  traceForm (family X r i) (family X s j)

/-- Exact off-diagonal pair marginals; reversed edges use the transpose.-/
def marginal (r s i j : Fin 3) : ℚ :=
  let P : Matrix (Fin 3) (Fin 3) ℚ := !![0,4/3,-1/3; 1/36,35/18,-35/36;35/36,-41/18,83/36]
  let Q : Matrix (Fin 3) (Fin 3) ℚ := !![-79951/7776,95107/3888,-102487/7776;90571/3888,-96223/1944,105763/3888;-93415/7776,101227/3888,-101263/7776]
  let R : Matrix (Fin 3) (Fin 3) ℚ := !![0,5/18,13/18;4/3,13/9,-16/9;-1/3,-13/18,37/18]
  match r.val, s.val with
  | 0, 1 => P i j
  | 1, 0 => P j i
  | 1, 2 => Q i j
  | 2, 1 => Q j i
  | 2, 0 => R i j
  | 0, 2 => R j i
  | _, _ => 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem pair_eq_marginal (r s i j : Fin 3) (hrs : r ≠ s) :
    pair witnessTheta1 r s i j = marginal r s i j := by
  fin_cases r <;> fin_cases s <;> try contradiction
  all_goals
    simp only [pair, family, AlbertLean.encoder, witnessTheta1]
    fin_cases i <;> fin_cases j <;>
      simp only [projector, theta1E_square, theta1F_square, theta1K_square]
  all_goals
      norm_num [
        traceForm_eq_fast, traceLinearForm, spurPairForm,
        Theta1ESquare, Theta1FSquare, Theta1KSquare,
        theta1E, theta1F, theta1K, one, v, q, marginal, Fin.isValue]

end OneBit.Closeout
