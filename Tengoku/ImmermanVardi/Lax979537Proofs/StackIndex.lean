import Tengoku.ImmermanVardi.Lax979537Proofs.StackHorner

namespace Lax979537Proofs.StackIndex

open StackProgram StackTransfer StackHorner

variable {K Aux : Type} [DecidableEq K]

def build (domain index counter tmp : K) : List K → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | coord :: rest => .seq (step domain index counter tmp coord) (build domain index counter tmp rest)

def value (n : Nat) (coords : List K) (v : K → Nat) (a : Nat) : Nat :=
  coords.foldl (fun a coord => n * a + v coord) a

def budget (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (7 * n + 9) + (n + 1) * budget n k

noncomputable def costPolynomial : Nat → Polynomial Nat
  | 0 => 1
  | k + 1 => (7 * Polynomial.X + 9) + (Polynomial.X + 1) * costPolynomial k

/--
@isnad1 id=eq.0h2v.s3.289259df481d from=translated src=- shape=e1571409 vocab=e30270e1
-/
theorem eval_costPolynomial (n k : Nat) : (costPolynomial k).eval n = budget n k := by
  induction k with
  | zero => simp [costPolynomial, budget]
  | succ k ih => simp [costPolynomial, budget, ih]

end Lax979537Proofs.StackIndex
