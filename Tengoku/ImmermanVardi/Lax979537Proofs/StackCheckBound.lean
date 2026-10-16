import Tengoku.ImmermanVardi.Lax979537Proofs.StackCompare
import Tengoku.ImmermanVardi.Lax979537Proofs.StackCopy

namespace Lax979537Proofs.StackCheckBound

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def save : BitProgram K ((Aux × Bool) × Bool) :=
  .atom (.load (fun s => (((s.1.1.1, s.1.2), true), none)))

def restore : BitProgram K ((Aux × Bool) × Bool) :=
  .atom (.load (fun s => (((s.1.1.1, true), s.1.1.2 && s.1.2), none)))

/-- Test one unary coordinate against the domain size, preserving both
arguments and accumulating validity. The spare control bit is reset to true. -/
def checkBound (left right copyLeft copyRight tmp : K) : BitProgram K ((Aux × Bool) × Bool) :=
  .seq save (.seq (StackCopy.copy left copyLeft tmp)
    (.seq (StackCopy.copy right copyRight tmp)
      (.seq (StackCompare.less copyLeft copyRight) restore)))

def result (left right : K) (s : BitStore K ((Aux × Bool) × Bool)) :
    BitStore K ((Aux × Bool) × Bool) :=
  ⟨(((s.state.1.1.1, true), s.state.1.2 && decide ((s.stk left).length < (s.stk right).length)),
    none), s.stk⟩

end Lax979537Proofs.StackCheckBound
