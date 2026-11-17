/-! Fixture of `tengoku-isnad --haves` (isnad.py tagtest): `two_haves`, `padded` (an unused `have` added) and `reordered` have the same two waypoints; `none_here` has none; `with_local` has one, closed over its variables; `with_let` has one whose statement mentions a `let` variable, and it comes out closed over `n` alone (the `let` is reduced away). `reordered` has the same two INDEPENDENT haves as `two_haves` in the opposite order. -/
namespace IsnadWp
theorem two_haves (a b : Nat) (h : a < b) : a ≤ b + 1 := by
  have h1 : a ≤ b := Nat.le_of_lt h
  have h2 : b ≤ b + 1 := Nat.le_succ b
  exact Nat.le_trans h1 h2

theorem padded (a b : Nat) (h : a < b) : a ≤ b + 1 := by
  have junk : a = a := rfl
  have h1 : a ≤ b := Nat.le_of_lt h
  have h2 : b ≤ b + 1 := Nat.le_succ b
  exact Nat.le_trans h1 h2

theorem reordered (a b : Nat) (h : a < b) : a ≤ b + 1 := by
  have h2 : b ≤ b + 1 := Nat.le_succ b
  have h1 : a ≤ b := Nat.le_of_lt h
  exact Nat.le_trans h1 h2

theorem none_here (n : Nat) : n = n := rfl

theorem with_local (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ k ih =>
    have step : k + 1 + b = (k + b) + 1 := by omega
    rw [step, ih]; omega

theorem with_let (n : Nat) : n + 0 = n := by
  let x := n
  have h : x + 0 = x := Nat.add_zero x
  exact h

end IsnadWp
