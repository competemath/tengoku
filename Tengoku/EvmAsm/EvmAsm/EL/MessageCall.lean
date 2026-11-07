/-
  EvmAsm.EL.MessageCall

  Pure message-call frame and result surface for GH #121.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.WorldState

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL

/-- CALL-family variants modeled by the first message-call layer.-/
inductive CallKind where
  | call
  | staticcall
  | delegatecall
  deriving DecidableEq, Repr

namespace CallKind

/-- Whether the call kind transfers value from caller to callee.-/
def transfersValue : CallKind → Bool
  | call => true
  | staticcall => false
  | delegatecall => false

/-- Whether the callee is allowed to write state in this call mode.-/
def mayWriteState : CallKind → Bool
  | call => true
  | staticcall => false
  | delegatecall => true

/-- Whether execution preserves the caller/value context from the parent frame.-/
def preservesCallerContext : CallKind → Bool
  | call => false
  | staticcall => false
  | delegatecall => true

/--
@isnad1 id=eq.0h0v.s2.815f2f3d7e86 from=translated src=- shape=4b736592 vocab=51e87400
-/
theorem transfersValue_call : transfersValue call = true := rfl
/--
@isnad1 id=eq.0h0v.s2.18f5b2023b01 from=translated src=- shape=4b736592 vocab=271ec018
-/
theorem transfersValue_staticcall : transfersValue staticcall = false := rfl
/--
@isnad1 id=eq.0h0v.s2.cdfffcc40528 from=translated src=- shape=4b736592 vocab=6439a2ee
-/
theorem transfersValue_delegatecall : transfersValue delegatecall = false := rfl

/--
@isnad1 id=eq.0h0v.s2.c8fe6173acaf from=translated src=- shape=4b736592 vocab=d7f9fc9a
-/
theorem mayWriteState_staticcall : mayWriteState staticcall = false := rfl
/--
@isnad1 id=eq.0h0v.s2.0171c811e283 from=translated src=- shape=4b736592 vocab=c48cb6a3
-/
theorem preservesCallerContext_delegatecall : preservesCallerContext delegatecall = true := rfl

end CallKind

/-- Pure input frame for one message-call execution.-/
structure CallFrame where
  kind : CallKind
  caller : Address
  callee : Address
  apparentValue : Word256
  transferredValue : Word256
  input : List Byte
  gas : Nat
  isStatic : Bool
  deriving Repr

namespace CallFrame

/-- CALL frame: value is both apparent to the callee and transferred.-/
def forCall
    (caller callee : Address) (value : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) : CallFrame :=
  { kind := .call
    caller := caller
    callee := callee
    apparentValue := value
    transferredValue := value
    input := input
    gas := gas
    isStatic := isStatic }

/-- STATICCALL frame: no value transfer and state writes are forbidden.-/
def forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) : CallFrame :=
  { kind := .staticcall
    caller := caller
    callee := callee
    apparentValue := 0
    transferredValue := 0
    input := input
    gas := gas
    isStatic := true }

/-- DELEGATECALL frame: caller/value context is preserved and no value is transferred.-/
def forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) : CallFrame :=
  { kind := .delegatecall
    caller := caller
    callee := callee
    apparentValue := apparentValue
    transferredValue := 0
    input := input
    gas := gas
    isStatic := isStatic }

/--
@isnad1 id=eq.0h6v.s4.33a0bb137bd1 from=translated src=- shape=29cb5d50 vocab=a610af3e
-/
theorem transferredValue_forCall
    (caller callee : Address) (value : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forCall caller callee value input gas isStatic).transferredValue = value := rfl

/--
@isnad1 id=eq.0h4v.s4.4f5954ca7882 from=translated src=- shape=f92ade94 vocab=d636b465
-/
theorem transferredValue_forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) :
    (forStaticCall caller callee input gas).transferredValue = 0 := rfl

/--
@isnad1 id=eq.0h6v.s5.06fb624c59ec from=translated src=- shape=85086f1b vocab=475bec2c
-/
theorem transferredValue_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forDelegateCall caller callee apparentValue input gas isStatic).transferredValue = 0 := rfl

/--
@isnad1 id=eq.0h4v.s4.d1ec3b7467c9 from=translated src=- shape=feffed4a vocab=23ed01c3
-/
theorem isStatic_forStaticCall
    (caller callee : Address) (input : List Byte) (gas : Nat) :
    (forStaticCall caller callee input gas).isStatic = true := rfl

/--
@isnad1 id=eq.0h6v.s4.f89ef358ee94 from=translated src=- shape=a4351db9 vocab=ebd07edc
-/
theorem kind_forDelegateCall
    (caller callee : Address) (apparentValue : Word256) (input : List Byte) (gas : Nat)
    (isStatic : Bool) :
    (forDelegateCall caller callee apparentValue input gas isStatic).kind = .delegatecall := rfl

end CallFrame

/-- Coarse result status for one message-call execution.-/
inductive CallStatus where
  | success
  | revert
  | failure
  deriving DecidableEq, Repr

namespace CallResult

end CallResult

end EvmAsm.EL
