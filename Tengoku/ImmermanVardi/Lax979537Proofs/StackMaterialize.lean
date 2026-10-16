import Tengoku.ImmermanVardi.Lax979537Proofs.StackTuples
import Tengoku.ImmermanVardi.Lax979537Proofs.StackBoolean

namespace Lax979537Proofs.StackMaterialize

open StackProgram StackTransfer StackFor StackTuples StackBoolean

variable {K Aux : Type} [DecidableEq K]

def emit (rev : K) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq body (.seq (save rev) (answer false))

def materialize (domain tmp rev out : K) (slots : List (K × K))
    (body : EvalProgram K Aux) : EvalProgram K Aux :=
  .seq (answer false) (.seq (forTuples domain tmp (emit rev body) slots) (transfer rev out))

def payload (s : EvalStore K Aux) (rev : K) (bits : List Bool) : EvalStore K Aux :=
  setStack (result false s) rev (bits ++ s.stk rev)

def table (n k : Nat) (b : List Nat → Bool) : List Bool := (tuples n k).map b

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackTuples.costPolynomial (B + 2) k + 3 * Polynomial.X ^ k + 3

end Lax979537Proofs.StackMaterialize
