import Tengoku.ImmermanVardi.Lax979537Proofs.StackPower
import Tengoku.ImmermanVardi.Lax979537Proofs.StackFor

namespace Lax979537Proofs.StackStages

open StackProgram StackTransfer StackFor

variable {K Aux α : Type} [DecidableEq K]

def prepared (base : α → BitStore K Aux) (bound : K) (m : Nat) (a : α) : BitStore K Aux :=
  ⟨((base a).state.1, none), Function.update (base a).stk bound (List.replicate m true)⟩

/-- Prepare the polynomial stage bound on a stack, run a fixed body under
that bound, and remove the bound. Neither n nor its power occurs in the code. -/
def stages (domain bound counter coord tmp : K) (powerCounters : List K)
    (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (StackPower.power domain bound tmp powerCounters)
    (.seq (forValues bound counter coord tmp body) (StackClear.clear bound))

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackPower.costPolynomial k + (B + 14) * Polynomial.X ^ k + 10

theorem foldRange_iterate (f : α → α) (start count : Nat) (a : α) :
    foldRange (fun _ => f) start count a = (f^[count]) a := by
  induction count generalizing start a with
  | zero => rfl
  | succ count ih => simp [foldRange, ih, Function.iterate_succ_apply]

end Lax979537Proofs.StackStages
