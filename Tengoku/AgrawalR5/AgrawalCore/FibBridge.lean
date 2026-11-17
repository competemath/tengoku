/-
Nucleo Lean della campagna Agrawal (S45) — lotto 4: il ponte di
divisibilità. Dal cuore aureo (InertiaCore) alle forme concrete:
  · `inertia_J_fib`   : p inerte, n pari,   p ∣ F_n,  5^(n−1) ≡ 1 → assurdo
  · `inertia_J_lucas` : p inerte, n dispari, p ∣ L_n,  5^(n−1) ≡ 1 → assurdo
cioè: nessun primo inerte divide J_n = gcd(B_n, 5^(n−1) − 1), con
B_n = F_n (n pari) / L_n (n dispari). Lucas via Fibonacci:
L_n = F_(n+1) + F_(n−1). Il quadrato F_(n−1)² = (−1)^n mod p ∣ F_n
esce dal prodotto delle due radici auree, senza identità esterne.
Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.InertiaCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- L'altra radice aurea `ε' = 1 − ε`.-/
noncomputable def eps' : GoldenRing p := 1 - eps

lemma eps'_sq : (eps' : GoldenRing p) ^ 2 = eps' + 1 := by
  have h := eps_sq (p := p)
  unfold eps'
  linear_combination h

lemma eps_mul_eps' : (eps : GoldenRing p) * eps' = -1 := by
  have h := eps_sq (p := p)
  unfold eps'
  linear_combination -h

omit [Fact p.Prime] in
/-- Potenze di una qualunque radice dell'equazione aurea, via Fibonacci.-/
lemma golden_pow_of_sq {x : GoldenRing p} (hx : x ^ 2 = x + 1) :
    ∀ n : ℕ, x ^ (n + 1)
      = (Nat.fib (n + 1) : GoldenRing p) * x + (Nat.fib n : GoldenRing p)
  | 0 => by simp
  | n + 1 => by
    have ih := golden_pow_of_sq hx n
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    linear_combination (Nat.fib (n + 1) : GoldenRing p) * hx

omit [Fact p.Prime] in
lemma golden_pow_pred {x : GoldenRing p} (hx : x ^ 2 = x + 1) {n : ℕ}
    (hn : 1 ≤ n) : x ^ n
      = (Nat.fib n : GoldenRing p) * x + (Nat.fib (n - 1) : GoldenRing p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using golden_pow_of_sq hx m

/-- Cast a zero nell'anello aureo di un naturale divisibile per `p`.-/
lemma natCast_eq_zero_of_dvd {a : ℕ} (h : p ∣ a) :
    ((a : ℕ) : GoldenRing p) = 0 := by
  have h1 : ((a : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h
  have h2 : ((a : ℕ) : GoldenRing p)
      = AdjoinRoot.of (goldenPoly p) ((a : ℕ) : ZMod p) := (map_natCast _ _).symm
  rw [h2, h1, map_zero]

/-- Se `p ∣ F_n` con `n ≥ 1` pari, allora `ε^(2n) = 1`.-/
lemma pow_eq_one_of_dvd_fib {n : ℕ} (hn : 1 ≤ n) (hev : Even n)
    (hdvd : p ∣ Nat.fib n) : (eps : GoldenRing p) ^ (2 * n) = 1 := by
  have hcast : ((Nat.fib n : ℕ) : GoldenRing p) = 0 := natCast_eq_zero_of_dvd hdvd
  have he := golden_pow_pred (eps_sq (p := p)) hn
  have he' := golden_pow_pred (eps'_sq (p := p)) hn
  rw [hcast, zero_mul, zero_add] at he he'
  obtain ⟨m, hm⟩ := hev
  have hprod : ((Nat.fib (n - 1) : ℕ) : GoldenRing p)
      * ((Nat.fib (n - 1) : ℕ) : GoldenRing p) = 1 := by
    calc ((Nat.fib (n - 1) : ℕ) : GoldenRing p) * _
        = eps ^ n * eps' ^ n := by rw [he, he']
      _ = (eps * eps') ^ n := (mul_pow _ _ _).symm
      _ = (-1 : GoldenRing p) ^ n := by rw [eps_mul_eps']
      _ = ((-1 : GoldenRing p) ^ 2) ^ m := by
          rw [← pow_mul]
          congr 1
          omega
      _ = 1 := by norm_num
  calc (eps : GoldenRing p) ^ (2 * n) = (eps ^ n) ^ 2 := by
        rw [← pow_mul, Nat.mul_comm]
    _ = 1 := by rw [he]; linear_combination hprod

/-- I numeri di Lucas via Fibonacci: `L_n = F_(n+1) + F_(n−1)`.-/
def lucas (n : ℕ) : ℕ := Nat.fib (n + 1) + Nat.fib (n - 1)

/-- `ε^n + ε'^n = L_n` nell'anello aureo (n ≥ 1).-/
lemma eps_pow_add_eps'_pow {n : ℕ} (hn : 1 ≤ n) :
    (eps : GoldenRing p) ^ n + eps' ^ n = (lucas n : GoldenRing p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [golden_pow_pred (eps_sq (p := p)) hn,
      golden_pow_pred (eps'_sq (p := p)) hn]
  unfold lucas eps'
  push_cast [Nat.fib_add_two]
  ring

/-- Se `p ∣ L_n` con `n ≥ 1` dispari, allora `ε^(2n) = 1`.-/
lemma pow_eq_one_of_dvd_lucas {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n)
    (hdvd : p ∣ lucas n) : (eps : GoldenRing p) ^ (2 * n) = 1 := by
  have hL : ((lucas n : ℕ) : GoldenRing p) = 0 := natCast_eq_zero_of_dvd hdvd
  have hsum := eps_pow_add_eps'_pow (p := p) hn
  rw [hL] at hsum
  have hneg : (eps : GoldenRing p) ^ n = - eps' ^ n := by
    linear_combination hsum
  have hm : (eps : GoldenRing p) ^ n * eps' ^ n = -1 := by
    rw [← mul_pow, eps_mul_eps']
    exact hodd.neg_one_pow
  have h2 : (eps' : GoldenRing p) ^ n * eps' ^ n = 1 := by
    rw [hneg] at hm
    linear_combination -hm
  calc (eps : GoldenRing p) ^ (2 * n) = eps ^ n * eps ^ n := by
        rw [two_mul, pow_add]
    _ = eps' ^ n * eps' ^ n := by rw [hneg]; ring
    _ = 1 := h2

/-- **Teorema d'inerzia di `J_n`, forma di divisibilità (n pari).**
Nessun primo `p` inerte in `Q(√5)` divide `gcd(F_n, 5^(n−1) − 1)`
per `n ≥ 1` pari.-/
theorem inertia_J_fib (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 ≤ n) (hev : Even n) (hdvd : p ∣ Nat.fib n)
    (h1 : (5 : ZMod p) ^ (n - 1) = 1) : False :=
  inertia_J h5 hp2 hn (pow_eq_one_of_dvd_fib hn hev hdvd) h1

/-- **Teorema d'inerzia di `J_n`, forma di divisibilità (n dispari).**
Nessun primo `p` inerte in `Q(√5)` divide `gcd(L_n, 5^(n−1) − 1)`
per `n` dispari.-/
theorem inertia_J_lucas (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) (hdvd : p ∣ lucas n)
    (h1 : (5 : ZMod p) ^ (n - 1) = 1) : False :=
  inertia_J h5 hp2 hn (pow_eq_one_of_dvd_lucas hn hodd hdvd) h1

end AgrawalCore
