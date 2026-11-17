/-
Nucleo Lean della campagna Agrawal (S45) — lotto 1: il lemma dell'indice.
Stile mathlib, zero ridondanza. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.Seed.Data.Nat.GCD.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- **Lemma dell'indice.** Se `x` e `y` dividono `M`, allora
`x * y ∣ gcd x y * M`. In particolare due divisori con prodotto
maggiore di `gcd x y * M` non esistono: la forma quantitativa
`gcd x y ≥ x * y / M` usata nella campagna.-/
theorem mul_dvd_gcd_mul {x y M : ℕ} (hx : x ∣ M) (hy : y ∣ M) :
    x * y ∣ Nat.gcd x y * M :=
  (Nat.gcd_mul_lcm x y) ▸ mul_dvd_mul_left _ (Nat.lcm_dvd hx hy)

/-- Forma estremale: se `gcd x y = 1` il prodotto stesso divide `M`
(già in mathlib come `Nat.Coprime.mul_dvd_of_dvd_of_dvd`; qui come
corollario nominato per il paper). I tre profili J della campagna
saturano questa divisibilità con uguaglianza.-/
theorem coprime_mul_dvd {x y M : ℕ} (h : Nat.Coprime x y)
    (hx : x ∣ M) (hy : y ∣ M) : x * y ∣ M :=
  h.mul_dvd_of_dvd_of_dvd hx hy

end AgrawalCore
