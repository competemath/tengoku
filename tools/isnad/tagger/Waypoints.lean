/-! Fixture of `tengoku-isnad --haves` (isnad.py tagtest): `two_haves`, `padded` (an unused `have` added) and `reordered` have the same two waypoints; `none_here` has none; `with_local` has one, closed over its variables. -/
namespace IsnadWp
theorem two_haves (a b : Nat) (h : a < b) : a + 1 ≤ b + 1 := by
  have h1 : a ≤ b := Nat.le_of_lt h
  have h2 : a + 1 ≤ b + 1 := Nat.succ_le_succ h1
  exact h2

theorem padded (a b : Nat) (h : a < b) : a + 1 ≤ b + 1 := by
  have junk : a = a := rfl
  have h1 : a ≤ b := Nat.le_of_lt h
  have h2 : a + 1 ≤ b + 1 := Nat.succ_le_succ h1
  exact h2

theorem reordered (a b : Nat) (h : a < b) : a + 1 ≤ b + 1 := by
  have h1 : a ≤ b := Nat.le_of_lt h
  have h2 : a + 1 ≤ b + 1 := Nat.succ_le_succ h1
  exact h2

theorem none_here (n : Nat) : n = n := rfl

theorem with_local (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ k ih =>
    have step : k + 1 + b = (k + b) + 1 := by omega
    rw [step, ih]; omega
end IsnadWp
