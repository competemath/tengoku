/-
Nucleo Lean della campagna Agrawal — lotto 13: IL CUORE LOCALE DI LENSTRA.

Obiettivo del lotto: per `p ≡ 3 (mod 80)` e `n` che soddisfa le due condizioni
di Korselt, dimostrare la congruenza di Agrawal nella componente ciclotomica,
    (ζ−1)^n = ζ^n − 1   in  F_p[X]/Φ₅ .

La riduzione. Posto `u = ζ − 1` e `w = 1 + ζ + ζ²` si ha `u·w = ζ³ − 1`
(somma geometrica), e il Frobenius dà `u^p = ζ³ − 1 = u·w`. Scrivendo
`n − 1 = a(p−1)` e usando `ζ^n = ζ³` (da `n ≡ 3 mod 5`), la tesi diventa
`w^a = w`.

Le due costanti del problema. Entrambe le relazioni che governano il calcolo
producono lo stesso fattore `−ζ⁴`:
  · `u^(p²) = −ζ⁴ · u`      (lotto 12, `order_bound_relation`)
  · `w^(p+1) = −ζ⁴`         (qui, `w_pow_p_succ`)
e quel fattore ha ordine 10, il che è esattamente il `10` del lemma
dell'ordine limitato e, di riflesso, il `5` che compare nel modulo 80.

Dichiarazioni di questo lotto:
  · `wElt`            : l'elemento `1 + ζ + ζ²`
  · `u_mul_w`         : `(ζ−1)·w = ζ³ − 1`
  · `u_pow_p`         : `(ζ−1)^p = (ζ−1)·w`            (p ≡ 3 mod 5)
  · `w_pow_p`         : `w^p = 1 + ζ + ζ³`             (p ≡ 3 mod 5)
  · `w_pow_p_succ`    : `w^(p+1) = −ζ⁴`
Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.OrderBound
import Tengoku.AgrawalR5.AgrawalCore.SupportBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- L'elemento `w = 1 + ζ + ζ²`, cofattore di `ζ−1` in `ζ³−1`.-/
noncomputable def wElt (p : ℕ) [Fact p.Prime] : Phi5Ring p :=
  1 + zeta5 + zeta5 ^ 2

/-- Somma geometrica: `(ζ−1)(1+ζ+ζ²) = ζ³−1`.-/
lemma u_mul_w : ((zeta5 : Phi5Ring p) - 1) * wElt p = zeta5 ^ 3 - 1 := by
  unfold wElt; ring

/-- Per `p ≡ 3 (mod 5)` il Frobenius manda `ζ−1` in `(ζ−1)·w`.-/
lemma u_pow_p (hp : p % 5 = 3) :
    ((zeta5 : Phi5Ring p) - 1) ^ p = (zeta5 - 1) * wElt p := by
  rw [zeta_sub_one_pow_p, hp, u_mul_w]

/-- Per `p ≡ 3 (mod 5)`, `w^p = 1 + ζ + ζ³`: il Frobenius permuta gli
esponenti moltiplicandoli per 3 modulo 5, e `{0,1,2} ↦ {0,3,6=1}`.-/
lemma w_pow_p (hp : p % 5 = 3) :
    (wElt p) ^ p = 1 + zeta5 ^ 3 + zeta5 := by
  unfold wElt
  rw [add_pow_char, add_pow_char, one_pow, ← pow_mul]
  have h1 : (zeta5 : Phi5Ring p) ^ p = zeta5 ^ 3 := by
    rw [zeta5_pow_mod, hp]
  have h2 : (zeta5 : Phi5Ring p) ^ (2 * p) = zeta5 := by
    rw [zeta5_pow_mod, Nat.mul_mod, hp]
    norm_num
  rw [h1, h2]

/-- **La seconda costante.** `w^(p+1) = −ζ⁴`, lo stesso fattore che compare
in `order_bound_relation`. Si ottiene moltiplicando `w` per `w^p` e riducendo
con `1+ζ+ζ²+ζ³+ζ⁴ = 0` e `ζ^5 = 1`.-/
theorem w_pow_p_succ (hp : p % 5 = 3) :
    (wElt p) ^ (p + 1) = -(zeta5 ^ 4 : Phi5Ring p) := by
  have hz : (zeta5 : Phi5Ring p) ^ 4 + zeta5 ^ 3 + zeta5 ^ 2 + zeta5 + 1 = 0 :=
    zeta5_rel
  have h5 : (zeta5 : Phi5Ring p) ^ 5 = 1 := zeta5_pow_five
  rw [pow_succ, w_pow_p hp]
  unfold wElt
  -- espandendo: 1 + 2ζ + 2ζ² + 2ζ³ + ζ⁴ + ζ⁵, e lo scarto dalla tesi è
  -- esattamente 2·(relazione ciclotomica) + (ζ⁵ = 1)
  linear_combination (2 : Phi5Ring p) * hz + h5

/-! ### Il ponte fra le due condizioni di Korselt

La condizione di Carmichael dà `n − 1 = a(p−1)`; quella di Lucas–Carmichael
dà `n ≡ −1 (mod p+1)`. Le due si parlano: poiché `p − 1 ≡ −2 (mod p+1)` e
`n − 1 ≡ −2 (mod p+1)`, dall'uguaglianza `n−1 = a(p−1)` segue
`−2a ≡ −2`, cioè `(p+1) ∣ 2(a−1)`. È il vincolo che, insieme a
`w^(p+1) = −ζ⁴`, controlla l'esponente `a` da cui dipende tutto il calcolo. -/

/-- Se `n − 1 = a(p−1)` e `p + 1` divide `n + 1`, allora `p + 1` divide
`2(a − 1)`. Enunciato su `ℤ` per evitare la sottrazione troncata.-/
theorem korselt_bridge {p n a : ℤ} (hcar : n - 1 = a * (p - 1))
    (hluc : (p + 1) ∣ (n + 1)) : (p + 1) ∣ 2 * (a - 1) := by
  obtain ⟨b, hb⟩ := hluc
  -- sottraendo le due ipotesi: (a+b) + p(b−a) = 2, che riordinata è
  -- 2(a−1) = (p+1)(a−b)
  exact ⟨a - b, by linear_combination hcar - hb⟩

/-! ### Il cuore

Le tre condizioni su `n` — Carmichael, Lucas–Carmichael, classe modulo 80 —
sono soddisfatte **anche da `p` stesso**: `p ≡ 1 (mod p−1)`,
`p ≡ −1 (mod p+1)`, `p ≡ 3 (mod 80)`. Dunque `n ≡ p` modulo
`lcm(p−1,\,p+1,\,80) = 10(p^2-1)`, che è esattamente il modulo del lemma
dell'ordine limitato. La congruenza di Agrawal segue allora dal Frobenius,
perché `(ζ−1)^n = (ζ−1)^p = ζ^3-1` e `ζ^n = ζ^p = ζ^3`. -/

/-- `ζ − 1` è invertibile: il prodotto dei quattro coniugati vale `5`, che è
un'unità appena `p ≠ 5`.-/
lemma zeta_sub_one_isUnit (hp5 : p ≠ 5) :
    IsUnit ((zeta5 : Phi5Ring p) - 1) := by
  have hprod : ((zeta5 : Phi5Ring p) - 1) *
      ((zeta5 ^ 2 - 1) * (zeta5 ^ 3 - 1) * (zeta5 ^ 4 - 1)) = 5 := by
    have h := prod_pow_sub_one (R := Phi5Ring p) (ζ := zeta5) zeta5_rel
    linear_combination h
  have h5 : IsUnit (5 : Phi5Ring p) := by
    have hz : IsUnit (5 : ZMod p) := (five_ne_zero hp5).isUnit
    have hmap := hz.map (algebraMap (ZMod p) (Phi5Ring p))
    rwa [map_ofNat] at hmap
  exact isUnit_of_mul_isUnit_left (hprod ▸ h5)

/-- Dal lemma dell'ordine limitato, in forma cancellata: `(ζ−1)^(10(p²−1)) = 1`.-/
theorem order_bounded_one (hp : p % 5 = 2 ∨ p % 5 = 3) (hp5 : p ≠ 5)
    (hp1 : 1 ≤ p) :
    ((zeta5 : Phi5Ring p) - 1) ^ (10 * (p * p - 1)) = 1 := by
  have hu := zeta_sub_one_isUnit (p := p) hp5
  have key : ((zeta5 : Phi5Ring p) - 1) ^ (10 * (p * p - 1)) *
      ((zeta5 : Phi5Ring p) - 1) ^ 10 = 1 * ((zeta5 : Phi5Ring p) - 1) ^ 10 := by
    rw [one_mul, ← pow_add]
    have harith : 10 * (p * p - 1) + 10 = 10 * (p * p) := by
      have : 1 ≤ p * p := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    rw [harith, order_bounded hp]
  exact (hu.pow 10).mul_left_cancel (by simpa [mul_comm] using key)

/-- **IL CUORE.** Se `n ≡ p` modulo `10(p²−1)` e `p ≡ 3 (mod 80)`, allora la
congruenza di Agrawal vale nella componente ciclotomica.-/
theorem lenstra_local {n k : ℕ} (hp80 : p % 80 = 3) (hp5 : p ≠ 5)
    (hn : n = p + k * (10 * (p * p - 1))) :
    ((zeta5 : Phi5Ring p) - 1) ^ n = zeta5 ^ n - 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hmod5 : p % 5 = 3 := by
    have hd : (5 : ℕ) ∣ 80 := by norm_num
    rw [← Nat.mod_mod_of_dvd p hd, hp80]
  have hone := order_bounded_one (p := p) (Or.inr hmod5) hp5 hp1
  -- (ζ−1)^n = (ζ−1)^p, perché l'eccedenza è un multiplo dell'ordine
  have hleft : ((zeta5 : Phi5Ring p) - 1) ^ n = (zeta5 - 1) ^ p := by
    rw [hn, pow_add, pow_mul', hone, one_pow, mul_one]
  -- ζ^n = ζ^p, perché 5 divide 10(p²−1)
  have hzeta : (zeta5 : Phi5Ring p) ^ n = zeta5 ^ p := by
    rw [hn, pow_add, pow_mul']
    have : ((zeta5 : Phi5Ring p) ^ (10 * (p * p - 1))) = 1 := by
      have h5 : 10 * (p * p - 1) = 5 * (2 * (p * p - 1)) := by ring
      rw [h5, pow_mul, zeta5_pow_five, one_pow]
    rw [this, one_pow, mul_one]
  rw [hleft, hzeta, zeta_sub_one_pow_p, hmod5, zeta5_pow_mod p, hmod5]

end AgrawalCore
