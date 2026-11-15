import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace Nat

def macaulayPow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a =>
      (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1) + 1).choose (d + 2) +
        macaulayPow d (a - (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)).choose (d + 1))

end Nat
