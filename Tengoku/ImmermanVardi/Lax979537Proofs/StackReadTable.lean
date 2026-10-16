import Tengoku.ImmermanVardi.Lax979537Proofs.StackTake
import Tengoku.ImmermanVardi.Lax979537Proofs.StackPower

namespace Lax979537Proofs.StackReadTable

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

/-- Read one dense relation table, using the unary domain size and a fixed
nesting depth. On insufficient input the validity bit becomes false. -/
def readTable (domain input table count tmp rev : K) (counters : List K) :
    BitProgram K (Aux × Bool) :=
  .seq (StackPower.power domain count tmp counters)
    (.seq (StackTake.takeBits count input rev) (transfer rev table))

def result (input table : K) (n k : Nat) (s : BitStore K (Aux × Bool)) : BitStore K (Aux × Bool) :=
  ⟨((s.state.1.1, s.state.1.2 && decide (n ^ k ≤ (s.stk input).length)), none),
    Function.update (Function.update s.stk input ((s.stk input).drop (n ^ k)))
      table (StackTake.paddedPrefix (n ^ k) (s.stk input))⟩

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  StackPower.costPolynomial k + Polynomial.C 7 * Polynomial.X ^ k + Polynomial.C 4

def cost (k n : Nat) : Nat := StackPower.cost k n + 7 * n ^ k + 4

theorem eval_costPolynomial (k n : Nat) : (costPolynomial k).eval n = cost k n := by
  simp [costPolynomial, cost, StackPower.eval_costPolynomial]

theorem result_preserves (input table key : K) (hi : key ≠ input) (ht : key ≠ table)
    (n k : Nat) (s : BitStore K (Aux × Bool)) :
    (result input table n k s).stk key = s.stk key := by
  simp [result, hi, ht]

end Lax979537Proofs.StackReadTable
