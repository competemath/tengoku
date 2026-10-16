import Tengoku.ImmermanVardi.Lax979537Proofs.StackRepeat

namespace Lax979537Proofs.StackPower

open StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

def addTokens (out : K) (m : Nat) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk out (List.replicate m true ++ s.stk out)⟩

/-- One copied domain counter per nesting level. Even the zero-th power
works on the empty domain: it contributes one token. -/
def power (domain out tmp : K) : List K → BitProgram K Aux
  | [] => .seq (.atom (.push out (fun _ => true)))
      (.atom (.load (fun s => (s.1, none))))
  | counter :: rest => .seq (StackCopy.copy domain counter tmp)
      (repeatCount counter (power domain out tmp rest))

def cost : Nat → Nat → Nat
  | 0, _ => 2
  | k + 1, n => 7 * n + 6 + n * (cost k n + 2)

noncomputable def costPolynomial : Nat → Polynomial Nat
  | 0 => Polynomial.C 2
  | k + 1 => Polynomial.C 7 * Polynomial.X + Polynomial.C 6 +
      Polynomial.X * (costPolynomial k + Polynomial.C 2)

theorem eval_costPolynomial (k n : Nat) : (costPolynomial k).eval n = cost k n := by
  induction k with
  | zero => simp [costPolynomial, cost]
  | succ k ih => simp [costPolynomial, cost, ih]

theorem addTokens_working (base : K → List Bool) (counter out : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) (m : Nat) :
    addTokens out m (working base counter out xs ys a scratch) =
      working base counter out xs (List.replicate m true ++ ys) a none := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hk : k = out <;> simp_all [addTokens, working]

end Lax979537Proofs.StackPower
