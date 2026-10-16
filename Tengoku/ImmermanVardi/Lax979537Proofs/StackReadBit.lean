import Tengoku.ImmermanVardi.Lax979537Proofs.StackLookup
import Tengoku.ImmermanVardi.Lax979537Proofs.StackBoolean
import Tengoku.ImmermanVardi.Lax979537Proofs.StackClear
import Tengoku.ImmermanVardi.Lax979537Proofs.StackTuples

namespace Lax979537Proofs.StackReadBit

open StackProgram StackTransfer StackBoolean StackTuples

variable {K Aux : Type} [DecidableEq K]

def popAnswer (buffer : K) : EvalProgram K Aux :=
  .atom (.pop buffer (fun s b => (((s.1.1.1, true), b.getD false), none)))

def readBit (table index buffer tmp : K) : EvalProgram K Aux :=
  .seq (StackCopy.copy table buffer tmp)
    (.seq (StackRepeat.repeatCount index (StackLookup.discard buffer))
      (.seq (popAnswer buffer) (StackClear.clear buffer)))

end Lax979537Proofs.StackReadBit
