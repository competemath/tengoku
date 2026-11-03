import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualFrameCoverage
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWordMatrixConnection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms matrixAction_standardCarrierProjector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms word_conjugates_projector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_jordanAut_to_standard_frame` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ActualFrameJordanAut

open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.QuaternionRow.WordMatrixConnection
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

def diagonalProjector (i : Fin 3) : Mat3 K :=
  fun r c => if r = i ∧ c = i then 1 else 0

/-- Literal standard carrier projector: the same diagonal rank-one `a` block
on `W` and `W*`, with both skew coordinates zero.-/
def standardCarrierProjector (i : Fin 3) : Carrier K :=
  ⟨grouped (diagonalProjector i) 0 0,
    grouped_symplectic_selfadjoint _ _ _⟩

theorem matrixAction_standardCarrierProjector (i : Fin 3) :
    matrixAction ((standardCarrierProjector (K := K) i : Carrier K) : Mat6 K) = standardProjector i := by
  apply LinearMap.ext
  intro x
  funext p
  rcases p with p | p <;> fin_cases p <;> fin_cases i <;>
    simp [matrixAction, standardCarrierProjector, standardProjector,
      coordinateLabel, grouped, diagonalProjector, hat,
      Fintype.sum_sum_type, Fin.sum_univ_succ]

/-- The matrix attached to a word conjugates every input projector whenever
the word intertwines its column action with the literal standard action.-/
theorem word_conjugates_projector
    (word : List (Step (K := K) (V := Vec6 K)))
    (P : Carrier K) (i : Fin 3)
    (hintertwine :
      (wordMap omega word).comp (matrixAction P) =
        (standardProjector i).comp (wordMap omega word)) :
    wordMatrix word * (P : Mat6 K) * inverseWordMatrix word =
      ((standardCarrierProjector (K := K) i : Carrier K) : Mat6 K) := by
  apply matrixAction_injective
  unfold wordMatrix inverseWordMatrix
  rw [matrixAction_mul, matrixAction_mul,
    matrixAction_matrixOfLinear, matrixAction_matrixOfLinear,
    matrixAction_standardCarrierProjector]
  calc
    ((wordMap omega word).comp (matrixAction P)).comp
        (wordMap omega (inverseWord word)) =
      ((standardProjector i).comp (wordMap omega word)).comp
        (wordMap omega (inverseWord word)) := by rw [hintertwine]
    _ = (standardProjector i).comp
        ((wordMap omega word).comp (wordMap omega (inverseWord word))) := by
      simp only [LinearMap.comp_assoc]
    _ = standardProjector i := by rw [inverseWord_right]; simp

/-- Actual trace-one self-adjoint projector frames are carried to the literal
standard frame by one genuine unital Jordan automorphism arising from exactly
twelve transvections.-/
theorem exists_jordanAut_to_standard_frame
    (P : Fin 3 → Carrier K)
    (hidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (htrace : ∀ i, jordanTrace (K := K) ((P i : Carrier K) : Mat6 K) = 1)
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    ∃ word : List (Step (K := K) (V := Vec6 K)), word.length = 12 ∧
      ∀ i, ((wordJordanAut word).linear (P i) : Carrier K) =
        standardCarrierProjector i := by
  obtain ⟨word, hlen, hintertwine⟩ :=
    exists_twelve_actual_carrier_frame_alignment P hidem htrace hsum
  refine ⟨word, hlen, ?_⟩
  intro i
  apply Subtype.ext
  exact word_conjugates_projector word (P i) i (hintertwine i)

end AlbertLean.Generic.QuaternionRow.ActualFrameJordanAut
