import Tengoku.ImmermanVardi.Lax979537Proofs.StackMaterialize

namespace Lax979537Proofs.StackTableRound

open StackProgram StackTransfer StackBoolean StackTuples StackMaterialize

variable {K Aux : Type} [DecidableEq K]

/-- Read the previous table throughout construction of the complete next
table. Only then discard the old table and install the new one. -/
def round (domain tmp rev current next : K) (slots : List (K × K))
    (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (materialize domain tmp rev next slots body)
    (.seq (StackClear.clear current)
      (.seq (transfer next rev) (transfer rev current)))

end Lax979537Proofs.StackTableRound
