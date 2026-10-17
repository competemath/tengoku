import Tengoku.ImmermanVardi.Lax979537Proofs.StackClear
import Tengoku.ImmermanVardi.Lax979537Proofs.StackBoolean

namespace Lax979537Proofs.StackOutput

open StackProgram StackTransfer StackBoolean

variable {K Aux : Type} [DecidableEq K]

/--
@isnad1 id=le.0h6v.s6.fca09d209bb2 from=translated src=- shape=141cd3f4 vocab=11cd9901
-/
theorem length_op {Γ : K → Type} {State : Type} (o : Op Γ State) (s : Store Γ State) (key : K) :
    ((o.apply s).stk key).length ≤ (s.stk key).length + 1 := by
  cases o with
  | push k f =>
      by_cases h : key = k
      · subst key; simp [Op.apply]
      · simp [Op.apply, h]
  | pop k f =>
      by_cases h : key = k
      · subst key; simp [Op.apply]; omega
      · simp [Op.apply, h]
  | peek k f | load f => simp [Op.apply]

/-- A deliberately coarse space bound, valid also on malformed inputs.
@isnad1 id=le.1h8v.s6.da8532965f5e from=translated src=- shape=b829de5b vocab=5f2fa55b
-/
theorem length_executes {Γ : K → Type} {State : Type} {p : Program Γ State}
    {s t : Store Γ State} {c : Nat} (h : Executes p s t c) (key : K) :
    (t.stk key).length ≤ (s.stk key).length + c := by
  induction h with
  | atom o s => exact length_op o s key
  | seq _ _ ihp ihq => omega
  | branch_true _ _ ih | branch_false _ _ ih => omega
  | loop_false _ => omega
  | loop_true _ _ _ ihp ihq => omega

def clearPorts : List K → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | key :: keys => .seq (StackClear.clear key) (clearPorts keys)

def cleared (keys : List K) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), fun key => if key ∈ keys then [] else s.stk key⟩

/-- Clear a fixed set of ports, emit the retained answer, and reset control. -/
def output (keys : List K) (port : K) (initial : ((Aux × Bool) × Bool) × Option Bool) : EvalProgram K Aux :=
  .seq (clearPorts keys)
    (.seq (.atom (.push port (fun s => s.1.2))) (.atom (.load (fun _ => initial))))

end Lax979537Proofs.StackOutput
