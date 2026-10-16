import Tengoku
import Lean.Elab.Tactic.Omega

namespace Lax979537Proofs.PolynomialBounds

open Polynomial

theorem eval_mono (p : Polynomial Nat) {n m : Nat} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial d c =>
      simpa only [eval_monomial] using
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left h d)

end Lax979537Proofs.PolynomialBounds
