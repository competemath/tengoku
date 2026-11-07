/-
  EvmAsm.EL.MessageCallExecution

  Pure execution hooks for message-call processing (GH #121).
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.Logs
public import Tengoku.EvmAsm.EvmAsm.EL.MessageCall

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL

namespace MessageCallExecution
/-- Side effects surfaced by the executable-spec `MessageCallOutput`. The
    output bytes and committed state remain in `CallResult`/`CallerVisibleResult`;
    this record tracks the auxiliary effects that are cleared on errors.-/
structure CallSideEffects where
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address

def empty : CallSideEffects :=
  { refundCounter := 0
    logs := LogState.empty
    accountsToDelete := []
    touchedAccounts := [] }

/--
@isnad1 id=eq.0h0v.s3.a69a67bba8fe from=translated src=- shape=b0ae1d2b vocab=b00f97e8
-/
@[simp] theorem refundCounter_empty : empty.refundCounter = 0 := rfl
/--
@isnad1 id=eq.0h0v.s2.0685cc0b5421 from=translated src=- shape=4b736592 vocab=085551cc
-/
@[simp] theorem logs_empty : empty.logs = LogState.empty := rfl
/--
@isnad1 id=eq.0h0v.s2.e1420500c042 from=translated src=- shape=0a817633 vocab=e5c80b81
-/
@[simp] theorem accountsToDelete_empty : empty.accountsToDelete = [] := rfl
/--
@isnad1 id=eq.0h0v.s2.0abe5d3db691 from=translated src=- shape=0a817633 vocab=a59558e9
-/
@[simp] theorem touchedAccounts_empty : empty.touchedAccounts = [] := rfl

/-- Executable-spec-shaped message-call output surface. Mirrors the Python
    `MessageCallOutput` fields while using `status` as the Lean error summary.-/
structure MessageCallOutput where
  gasLeft : Nat
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address
  status : CallStatus

end MessageCallExecution

end EvmAsm.EL
