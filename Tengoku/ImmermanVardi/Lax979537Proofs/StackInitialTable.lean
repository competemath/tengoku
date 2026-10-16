import Tengoku.ImmermanVardi.Lax979537Proofs.StackMaterialize

namespace Lax979537Proofs.StackInitialTable

open StackProgram StackTransfer StackTuples StackBoolean

variable {K Aux : Type} [DecidableEq K]

def emptyTable (domain tmp rev current : K) (slots : List (K × K)) : EvalProgram K Aux :=
  StackMaterialize.materialize domain tmp rev current slots (answer false)

end Lax979537Proofs.StackInitialTable
