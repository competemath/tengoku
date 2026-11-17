/-
Nucleo Lean della campagna Agrawal — lotto 12: L'ORDINE LIMITATO.

Il lemma dell'ordine limitato `T_p | 10(p²−1)` era stato verificato
numericamente (341 casi su 341, campagna del 23 luglio) e usato come
acceleratore del setaccio CRT, ma mai dimostrato. Qui si dimostra, e la
dimostrazione è di quattro righe una volta trovata la relazione giusta:

  u = ζ − 1  ⟹  u^(p²) = ζ^(p²) − 1 = ζ⁴ − 1 = ζ⁻¹ − 1 = −u·ζ⁴,

da cui `u^(p²−1) = −ζ⁴` e, elevando alla decima, `u^(10(p²−1)) = 1`.
Il segno e la radice quinta si annullano insieme: (−1)^10 = 1 e ζ^40 = 1.

  · `zeta5_pow_mod`        : ζ^m = ζ^(m % 5)
  · `zeta_sub_one_pow_p`   : (ζ−1)^p = ζ^(p % 5) − 1        (Frobenius)
  · `zeta_sub_one_pow_sq`  : (ζ−1)^(p·p) = ζ⁴ − 1           (p ≡ ±2 mod 5)
  · `order_bound_relation` : (ζ−1)^(p·p) = −ζ⁴ · (ζ−1)
  · `order_bounded`        : (ζ−1)^(10·(p·p−1)) = 1

Vale per entrambe le classi inerti, p ≡ 2 e p ≡ 3 mod 5: in un caso
ζ^p = ζ², nell'altro ζ^p = ζ³, e in entrambi ζ^(p²) = ζ⁴ perché
2² ≡ 3² ≡ 4 (mod 5). Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.AgrawalBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- L'anello ciclotomico ha la caratteristica del campo di base.-/
instance phi5_charP : CharP (Phi5Ring p) p :=
  charP_of_injective_algebraMap (phi5_of_injective) p

/-- `ζ^m` dipende solo da `m` modulo 5.-/
lemma zeta5_pow_mod (m : ℕ) :
    (zeta5 : Phi5Ring p) ^ m = zeta5 ^ (m % 5) := by
  conv_lhs => rw [← Nat.div_add_mod m 5]
  rw [pow_add, pow_mul, zeta5_pow_five, one_pow, one_mul]

/-- Il Frobenius manda `ζ − 1` in `ζ^(p mod 5) − 1`.-/
lemma zeta_sub_one_pow_p :
    ((zeta5 : Phi5Ring p) - 1) ^ p = zeta5 ^ (p % 5) - 1 := by
  rw [sub_pow_char, one_pow, ← zeta5_pow_mod]

/-- Per `p ≡ ±2 (mod 5)` (le due classi inerti) il quadrato del Frobenius
manda `ζ − 1` in `ζ⁴ − 1`, perché `2² ≡ 3² ≡ 4 (mod 5)`.-/
lemma zeta_sub_one_pow_sq (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ((zeta5 : Phi5Ring p) - 1) ^ (p * p) = zeta5 ^ 4 - 1 := by
  rw [pow_mul, zeta_sub_one_pow_p, sub_pow_char, one_pow, ← pow_mul,
    zeta5_pow_mod]
  rcases hp with h | h <;> simp [h, Nat.mul_mod]

/-- La relazione chiave: `(ζ−1)^(p²) = −ζ⁴·(ζ−1)`.
Viene da `ζ⁴ = ζ⁻¹`, quindi `ζ⁴ − 1 = (1−ζ)·ζ⁴ = −(ζ−1)·ζ⁴`.-/
theorem order_bound_relation (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ((zeta5 : Phi5Ring p) - 1) ^ (p * p) = -(zeta5 ^ 4) * (zeta5 - 1) := by
  rw [zeta_sub_one_pow_sq hp]
  have h5 : (zeta5 : Phi5Ring p) ^ 5 = 1 := zeta5_pow_five
  have : -(zeta5 ^ 4 : Phi5Ring p) * (zeta5 - 1)
      = zeta5 ^ 4 - zeta5 ^ 5 := by ring
  rw [this, h5]

/-- **L'ORDINE LIMITATO.** `(ζ−1)^(10·p²) = (ζ−1)^10`, cioè l'ordine di
`ζ − 1` divide `10(p²−1)`: il fattore `−ζ⁴` accumulato dal Frobenius si
annulla alla decima potenza, perché `(−1)^10 = 1` e `ζ^40 = (ζ^5)^8 = 1`.
Enunciato senza divisioni, quindi senza bisogno dell'invertibilità.
Verificato numericamente 341 volte su 341 il 23 luglio; qui è dimostrato.-/
theorem order_bounded (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ((zeta5 : Phi5Ring p) - 1) ^ (10 * (p * p)) = (zeta5 - 1) ^ 10 := by
  have hz40 : ((zeta5 : Phi5Ring p) ^ 4) ^ 10 = 1 := by
    rw [← pow_mul]
    have h40 : (4 * 10 : ℕ) = 5 * 8 := by norm_num
    rw [h40, pow_mul, zeta5_pow_five, one_pow]
  calc ((zeta5 : Phi5Ring p) - 1) ^ (10 * (p * p))
      = (((zeta5 : Phi5Ring p) - 1) ^ (p * p)) ^ 10 := by
        rw [← pow_mul, mul_comm]
    _ = (-(zeta5 ^ 4) * (zeta5 - 1)) ^ 10 := by rw [order_bound_relation hp]
    _ = ((zeta5 : Phi5Ring p) ^ 4) ^ 10 * (zeta5 - 1) ^ 10 := by ring
    _ = (zeta5 - 1) ^ 10 := by rw [hz40, one_mul]

end AgrawalCore
