import Tengoku.ImmermanVardi.Lax979537Proofs.StackStages
import Tengoku.ImmermanVardi.Lax979537Proofs.StackTableRound

namespace Lax979537Proofs.StackTableStages

open StackProgram StackTransfer StackFor StackTuples StackBoolean StackStages

variable {K Aux α : Type} [DecidableEq K]

def family (s : EvalStore K Aux) (current : K) (encode : α → List Bool) (a : α) : EvalStore K Aux :=
  setStack (result false s) current (encode a)

def running (s : EvalStore K Aux) (current bound counter coord : K)
    (encode : α → List Bool) (m : Nat) (a : α) (i remaining : Nat) (scratch : Option Bool) :
    EvalStore K Aux :=
  pack (prepared (family s current encode) bound m) counter coord a i remaining scratch

def tableStages (domain tmp rev current next bound counter coord : K)
    (powerCounters : List K) (tupleSlots : List (K × K)) (body : EvalProgram K Aux) : EvalProgram K Aux :=
  stages domain bound counter coord tmp powerCounters
    (StackTableRound.round domain tmp rev current next tupleSlots body)

def roundCost (n k B : Nat) : Nat := StackTuples.cost n (B + 2) k + 11 * n ^ k + 9

noncomputable def costPolynomial (B : Polynomial Nat) (k : Nat) : Polynomial Nat :=
  StackStages.costPolynomial
    (StackTuples.costPolynomial (B + 2) k + 11 * Polynomial.X ^ k + 9) k

end Lax979537Proofs.StackTableStages
