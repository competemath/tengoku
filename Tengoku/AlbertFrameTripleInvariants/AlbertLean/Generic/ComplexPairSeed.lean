import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowLabelledProbes
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms X_mul_Xi` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Xi_mul_X` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_encoder` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_commutator_det` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_commutator_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-! The rational conjugator, inverse, encoder and a 3x3 commutator determinant
for a nonempty complex-pair probe chart. -/

noncomputable section
namespace AlbertLean.Generic.ComplexPairSeed

open FourRowProbeTrace FourRowLabelledProbes

variable {K : Type*} [Field K] [CharZero K]

def X : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, 2, 3; 1, 5, 7]
def Xi : Matrix (Fin 3) (Fin 3) K :=
  (1 / 2 : K) • !![1, 2, -1; 4, -6, 2; -3, 4, -1]

/--
@isnad1 id=eq.0h1v.s7.d98484faeeb4 from=translated src=- shape=f5de78c6 vocab=deb9ccb7
-/
theorem X_mul_Xi : (X : Matrix (Fin 3) (Fin 3) K) * Xi = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Xi, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Fin.ext_iff]

/--
@isnad1 id=eq.0h1v.s7.00e38cb16c2d from=translated src=- shape=f5de78c6 vocab=deb9ccb7
-/
theorem Xi_mul_X : (Xi : Matrix (Fin 3) (Fin 3) K) * X = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Xi, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Fin.ext_iff]

def frame (i : Fin 3) : Matrix (Fin 3) (Fin 3) K := X * diagonalUnit i * Xi

/--
@isnad1 id=eq.0h1v.s9.2f9ff3948481 from=translated src=- shape=6961f42f vocab=330f4494
-/
theorem frame_encoder :
    encoder (frame 0 : Matrix (Fin 3) (Fin 3) K) (frame 2) =
      !![-2, 1, 0; -5, 5, -1; -11, 13, -3] := by
  have hf (l r c : Fin 3) : (frame l : Matrix (Fin 3) (Fin 3) K) r c =
      X r l * Xi l c := by
    fin_cases l <;> simp [frame, Matrix.mul_apply, diagonalUnit, Fin.sum_univ_succ]
  ext i j
  simp only [encoder, Matrix.sub_apply, hf]
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Xi, Matrix.cons_val_two]

/--
@isnad1 id=eq.0h1v.s8.9bee8795ef73 from=translated src=- shape=1ed18c98 vocab=28a870b3
-/
theorem frame_commutator_det :
    Matrix.det (grading * encoder (frame 0 : Matrix (Fin 3) (Fin 3) K) (frame 2) -
      encoder (frame 0) (frame 2) * grading) = 22 := by
  rw [frame_encoder, det_grading_commutator]
  norm_num [FourRowProbeSeparation.cycleDifference, Matrix.cons_val_two]

/--
@isnad1 id=ne.0h1v.s8.0185feff1c22 from=translated src=- shape=1ed18c98 vocab=28a870b3
-/
theorem frame_commutator_ne_zero :
    Matrix.det (grading * encoder (frame 0 : Matrix (Fin 3) (Fin 3) K) (frame 2) -
      encoder (frame 0) (frame 2) * grading) ≠ 0 := by
  rw [frame_commutator_det]
  norm_num

end AlbertLean.Generic.ComplexPairSeed
