/-
Nucleo Lean della campagna Agrawal (S45) — lotto 8: i corollari con
ipotesi aritmetiche pure (p mod 5), forma finale per il paper.
Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.SupportBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Inerzia di `J_n`, `n` pari, ipotesi aritmetica pura.-/
theorem inertia_J_fib_mod5 (hp : p % 5 = 2 ∨ p % 5 = 3) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 ≤ n) (hev : Even n) (hdvd : p ∣ Nat.fib n)
    (h1 : (5 : ZMod p) ^ (n - 1) = 1) : False :=
  inertia_J_fib (not_isSquare_five hp2 hp) hp2 hn hev hdvd h1

/-- Inerzia di `J_n`, `n` dispari (Lucas), ipotesi aritmetica pura.-/
theorem inertia_J_lucas_mod5 (hp : p % 5 = 2 ∨ p % 5 = 3) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) (hdvd : p ∣ lucas n)
    (h1 : (5 : ZMod p) ^ (n - 1) = 1) : False :=
  inertia_J_lucas (not_isSquare_five hp2 hp) hp2 hn hodd hdvd h1

end AgrawalCore
