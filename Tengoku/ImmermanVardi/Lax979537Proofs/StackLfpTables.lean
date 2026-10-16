import Tengoku.ImmermanVardi.Lax979537Proofs.StackInitialTable
import Tengoku.ImmermanVardi.Lax979537Proofs.StackTableStages

namespace Lax979537Proofs.StackLfpTables

open StackProgram StackTransfer StackTuples StackBoolean StackTableStages

variable {K Aux α : Type} [DecidableEq K]

def run (domain tmp rev current next bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K)) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (StackInitialTable.emptyTable domain tmp rev current tupleSlots)
    (tableStages domain tmp rev current next bound counter coord powerCounters tupleSlots body)

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackTuples.costPolynomial 3 k + 3 * Polynomial.X ^ k + 3 + StackTableStages.costPolynomial B k

end Lax979537Proofs.StackLfpTables
