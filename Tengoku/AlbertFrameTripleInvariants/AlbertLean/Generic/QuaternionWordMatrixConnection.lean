import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualFrameCoverage
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSymplecticConjugation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms matrixAction_matrixOfLinear` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverseWord_left` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverseWord_right` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wordMatrix_mul_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixAction_basisVector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symplectic_product_entry` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms omega_basisVector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrix_symplectic_of_action_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wordMatrix_symplectic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms wordJordanAut` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WordMatrixConnection

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.QuaternionRow.SymplecticConjugation
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Matrix whose `j`th column is the image of the `j`th literal coordinate
vector.-/
def matrixOfLinear (L : Vec6 K →ₗ[K] Vec6 K) : Mat6 K :=
  fun i j => L (basisVector j) i

theorem matrixAction_matrixOfLinear (L : Vec6 K →ₗ[K] Vec6 K) :
    matrixAction (matrixOfLinear L) = L := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, b, hx⟩ := standard_spans x
  rw [hx]
  simp only [map_add, map_sum, map_smul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · congr 1
    ext p
    simp [matrixAction, matrixOfLinear, standardE, basisVector,
      Pi.single_apply]
  · congr 1
    ext p
    simp [matrixAction, matrixOfLinear, standardF, basisVector,
      Pi.single_apply]

theorem inverseWord_left
    (word : List (Step (K := K) (V := Vec6 K))) :
    (wordMap omega (inverseWord word)).comp (wordMap omega word) = LinearMap.id := by
  induction word with
  | nil => rfl
  | cons step word ih =>
      rcases step with ⟨d, t⟩
      simp only [inverseWord, List.reverse_cons, List.map_append, List.map_singleton,
        wordMap_append, wordMap]
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      have hcancel := LinearMap.congr_fun
        (map_neg_comp omega omega_alternating d t) (wordMap omega word x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcancel
      rw [hcancel]
      exact LinearMap.congr_fun ih x

private theorem inverseWord_involutive
    (word : List (Step (K := K) (V := Vec6 K))) :
    inverseWord (inverseWord word) = word := by
  simp [inverseWord, Function.comp_def]

theorem inverseWord_right
    (word : List (Step (K := K) (V := Vec6 K))) :
    (wordMap omega word).comp (wordMap omega (inverseWord word)) = LinearMap.id := by
  have h := inverseWord_left (inverseWord word)
  rw [inverseWord_involutive] at h
  exact h

def wordMatrix (word : List (Step (K := K) (V := Vec6 K))) : Mat6 K :=
  matrixOfLinear (wordMap omega word)

def inverseWordMatrix (word : List (Step (K := K) (V := Vec6 K))) : Mat6 K :=
  matrixOfLinear (wordMap omega (inverseWord word))

theorem wordMatrix_mul_inverse (word : List (Step (K := K) (V := Vec6 K))) :
    wordMatrix word * inverseWordMatrix word = 1 := by
  apply matrixAction_injective
  unfold wordMatrix inverseWordMatrix
  rw [matrixAction_mul, matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
    inverseWord_right, matrixAction_one]

theorem inverse_mul_wordMatrix (word : List (Step (K := K) (V := Vec6 K))) :
    inverseWordMatrix word * wordMatrix word = 1 := by
  apply matrixAction_injective
  unfold wordMatrix inverseWordMatrix
  rw [matrixAction_mul, matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
    inverseWord_left, matrixAction_one]

/-- Acting on a literal coordinate vector reads the corresponding matrix
column.-/
theorem matrixAction_basisVector (M : Mat6 K) (j : Ix6) :
    matrixAction (K := K) M (basisVector (K := K) j) = fun i => M i j := by
  classical
  funext i
  rcases j with j | j <;> fin_cases j <;>
    simp [matrixAction, basisVector, Pi.single_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ]

/-- The `(i,j)` entry of `M transpose * J * M` is the literal symplectic
pairing of columns `i` and `j`.  The matrix indices remain abstract while the
two small summation indices are expanded.-/
theorem symplectic_product_entry (M : Mat6 K) (i j : Ix6) :
    ((M.transpose * (symplecticJ : Mat6 K) * M) : Mat6 K) i j =
      (omega (K := K)) (fun r => M r i) (fun r => M r j) := by
  simp [omega, omegaFun, symplecticJ, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
  ring

/-- The literal coordinate vectors have Gram matrix `J`.-/
theorem omega_basisVector (i j : Ix6) :
    (omega (K := K)) (basisVector (K := K) i) (basisVector (K := K) j) =
      symplecticJ i j := by
  classical
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [omega, omegaFun, symplecticJ, basisVector, Pi.single_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

/-- A flat action-level preservation statement implies the literal matrix
symplectic equation, through the three column identities above.-/
theorem matrix_symplectic_of_action_preserves
    (M : Mat6 K)
    (hpres : ∀ x y : Vec6 K,
      (omega (K := K)) (matrixAction (K := K) M x) (matrixAction (K := K) M y) =
        (omega (K := K)) x y) :
    M.transpose * symplecticJ * M = symplecticJ := by
  ext i j
  rw [symplectic_product_entry]
  rw [← matrixAction_basisVector M i, ← matrixAction_basisVector M j]
  rw [hpres]
  exact omega_basisVector i j

/-- Form preservation of the word is the literal matrix symplectic equation.-/
theorem wordMatrix_symplectic (word : List (Step (K := K) (V := Vec6 K))) :
    (wordMatrix word).transpose * symplecticJ * wordMatrix word = symplecticJ := by
  apply matrix_symplectic_of_action_preserves
  intro x y
  unfold wordMatrix
  rw [matrixAction_matrixOfLinear]
  exact wordMap_preserves (omega (K := K)) omega_alternating word x y

/-- Every finite transvection word therefore supplies a genuine unital Jordan
automorphism of the actual self-adjoint carrier.-/
def wordJordanAut (word : List (Step (K := K) (V := Vec6 K))) :
    ScalarJordanAut.Aut (K := K) :=
  jordanAut (wordMatrix word) (inverseWordMatrix word)
    (wordMatrix_mul_inverse word) (inverse_mul_wordMatrix word)
    (wordMatrix_symplectic word)

end AlbertLean.Generic.QuaternionRow.WordMatrixConnection
