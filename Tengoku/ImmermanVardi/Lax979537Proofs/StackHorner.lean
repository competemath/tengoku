import Tengoku.ImmermanVardi.Lax979537Proofs.StackPower

namespace Lax979537Proofs.StackHorner

open StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

/-- One unary Horner step: index := domain-size * index + coordinate.
The domain size and coordinate are read from their preserved stacks. -/
def step (domain index counter tmp coord : K) : BitProgram K Aux :=
  .seq (transfer index counter)
    (.seq (repeatCount counter (StackCopy.copy domain index tmp)) (StackCopy.copy coord index tmp))

def setIndex (s : BitStore K Aux) (index : K) (a : Nat) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk index (List.replicate a true)⟩

end Lax979537Proofs.StackHorner
