import Tengoku.ImmermanVardi.Lax979537Proofs.StackFor
import Tengoku.ImmermanVardi.Lax979537Proofs.StackBoolean

namespace Lax979537Proofs.StackExists

open StackProgram StackTransfer StackBoolean StackFor

variable {K Aux : Type} [DecidableEq K]

def accumulate (acc : K) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq body (.seq (combine acc (· || ·)) (.seq (save acc) (answer false)))

def finish (acc : K) : EvalProgram K Aux :=
  .atom (.pop acc (fun s b => (((s.1.1.1, true), b.getD false), none)))

/-- Existential quantification by an exhaustive scan of the domain. The
program is fixed independently of the domain size and the predicate. -/
def existsValues (domain counter coord tmp acc : K) (body : EvalProgram K Aux) :
    EvalProgram K Aux :=
  .seq (answer false) (.seq (save acc)
    (.seq (forValues domain counter coord tmp (accumulate acc body)) (finish acc)))

def payload (s : EvalStore K Aux) (acc : K) (a : Bool) : EvalStore K Aux :=
  ⟨(result false s).state, Function.update s.stk acc (a :: s.stk acc)⟩

/--
@isnad1 id=eq.0h4v.s5.4f9cc0c9f85f from=translated src=- shape=712ef83e vocab=cd071a56
-/
theorem fold_or (b : Nat → Bool) (start count : Nat) (a : Bool) :
    foldRange (fun i a => a || b i) start count a =
      (a || (List.range' start count).any b) := by
  induction count generalizing start a with
  | zero => simp [foldRange]
  | succ count ih => simp [foldRange, ih, List.range'_succ, Bool.or_assoc]

/--
@isnad1 id=iff.0h2v.s4.a49d53587153 from=translated src=- shape=dc820564 vocab=4c38ae4a
-/
theorem any_range_iff (b : Nat → Bool) (n : Nat) :
    (List.range n).any b = true ↔ ∃ i, i < n ∧ b i = true := by simp

end Lax979537Proofs.StackExists
