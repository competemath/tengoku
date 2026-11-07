/-
  EvmAsm.EL.Create

  Pure contract-creation request surface for GH #115.
-/

module

public import Tengoku.EvmAsm.EvmAsm.EL.WorldState

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace EvmAsm.EL

/-- CREATE-family opcode variant.-/
inductive CreateKind where
  | create
  | create2
  deriving DecidableEq, Repr

namespace CreateKind

def usesSalt : CreateKind → Bool
  | create => false
  | create2 => true

/--
@isnad1 id=eq.0h0v.s2.01435ae3142c from=translated src=- shape=4b736592 vocab=398e6416
-/
theorem usesSalt_create : usesSalt create = false := rfl
/--
@isnad1 id=eq.0h0v.s2.56cfe111a628 from=translated src=- shape=4b736592 vocab=1d0acb65
-/
theorem usesSalt_create2 : usesSalt create2 = true := rfl

end CreateKind

/-- Pure input request for a CREATE or CREATE2 operation.-/
structure CreateRequest where
  kind : CreateKind
  creator : Address
  value : Word256
  initcode : List Byte
  gas : Nat
  salt? : Option Word256
  deriving Repr

namespace CreateRequest

def forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    CreateRequest :=
  { kind := .create
    creator := creator
    value := value
    initcode := initcode
    gas := gas
    salt? := none }

def forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) : CreateRequest :=
  { kind := .create2
    creator := creator
    value := value
    initcode := initcode
    gas := gas
    salt? := some salt }

def isCreate2 (request : CreateRequest) : Prop :=
  request.kind = .create2

def hasSalt (request : CreateRequest) : Prop :=
  request.salt?.isSome

/--
@isnad1 id=eq.0h4v.s4.5f23bc841979 from=translated src=- shape=37ee9bbd vocab=ed1a38ed
-/
theorem kind_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    (forCreate creator value initcode gas).kind = .create := rfl

/--
@isnad1 id=eq.0h5v.s4.29758fe45087 from=translated src=- shape=73a268a9 vocab=e8f7e188
-/
theorem kind_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).kind = .create2 := rfl

/--
@isnad1 id=hassalt.0h5v.s4.e1dc2cc5a2db from=translated src=- shape=520aed0f vocab=c41084a4
-/
theorem hasSalt_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).hasSalt := by
  unfold hasSalt
  rfl

/--
@isnad1 id=not.0h4v.s4.666d2da1e91d from=translated src=- shape=50ce1eea vocab=4887929d
-/
theorem not_hasSalt_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    ¬ (forCreate creator value initcode gas).hasSalt := by
  simp [hasSalt, forCreate]

/--
@isnad1 id=iscreate.0h5v.s4.4ccb874889b9 from=translated src=- shape=520aed0f vocab=3639cab9
-/
theorem isCreate2_forCreate2
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat)
    (salt : Word256) :
    (forCreate2 creator value initcode gas salt).isCreate2 := rfl

/--
@isnad1 id=not.0h4v.s4.faa372116fed from=translated src=- shape=50ce1eea vocab=bc332baf
-/
theorem not_isCreate2_forCreate
    (creator : Address) (value : Word256) (initcode : List Byte) (gas : Nat) :
    ¬ (forCreate creator value initcode gas).isCreate2 := by
  simp [isCreate2, forCreate]

end CreateRequest

/-- Coarse result status for CREATE and CREATE2.-/
inductive CreateStatus where
  | deployed
  | reverted
  | failed
  deriving DecidableEq, Repr

namespace CreateResult

end CreateResult

end EvmAsm.EL
