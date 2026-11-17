/-
Nucleo Lean della campagna Agrawal — lotto 11: LA LEVA E IL BOX.

Certifica i passi algebrici dell'assalto al secondo muro (25 luglio 2026),
cioè al problema della vacuità di L = {Lucas–Carmichael} ∩ {pseudoprimi di
Fermat base 5} ∩ {n ≡ ±2 mod 5} per n con tre fattori primi.

1. `prod_pairs_sub_prod_squares`: l'identità che misura di quanto il prodotto
   sulle coppie supera il prodotto dei quadrati. È il motore del teorema del
   box: il difetto è una somma di quadrati pesati, quindi non negativo, e nullo
   solo nel caso degenere in cui i tre elementi coincidono. Vale in ogni anello
   commutativo.

2. `prod_pairs_ge_prod_squares`: la forma ordinata su ℤ. Nel nostro uso il
   prodotto dei tre quozienti vale 8·I_p·I_q·I_r moltiplicato per il rapporto
   fra i due prodotti; questa disuguaglianza è ciò che costringe quel prodotto
   di interi a saltare di almeno uno, ed è da lì che nasce il box.

3. `lt_two_mul_of_sq_le`: il passo di taglia. Se r² ≤ 2·I·p·q e q < r, allora
   r < 2·I·p: in una tripla di L il fattore massimo è al più 2·I_r volte il
   minimo. Indici limitati implicano dunque fattori limitati, cioè una
   casistica finita ed enumerabile.

Campagna UNICO, 25 luglio 2026.
-/
import Tengoku.Seed.Data.Nat.GCD.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- **L'identità della leva.** In ogni anello commutativo, il doppio dello
scarto fra il prodotto sulle coppie `(xy − 1)` e il prodotto dei `(x² − 1)` è
la somma dei quadrati delle differenze, pesati dai `(x² − 1)`.
@isnad1 id=eq.0h4v.s9.8867d9f1f0ec from=translated src=- shape=9e5e2bd1 vocab=9c1cdc1d
-/
theorem prod_pairs_sub_prod_squares {R : Type*} [CommRing R] (p q r : R) :
    2 * ((p * q - 1) * (p * r - 1) * (q * r - 1)
          - (p ^ 2 - 1) * (q ^ 2 - 1) * (r ^ 2 - 1))
      = (p ^ 2 - 1) * (q - r) ^ 2
        + (q ^ 2 - 1) * (p - r) ^ 2
        + (r ^ 2 - 1) * (p - q) ^ 2 := by
  ring

/-- **La forma ordinata.** Per interi con `1 ≤ p, q, r`, il prodotto sulle
coppie domina il prodotto dei quadrati: il difetto è, per l'identità
precedente, una somma di termini non negativi.
@isnad1 id=le.3h3v.s7.09c3957e7d5e from=translated src=- shape=313b3ef9 vocab=01fb1e56
-/
theorem prod_pairs_ge_prod_squares {p q r : ℤ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    (p ^ 2 - 1) * (q ^ 2 - 1) * (r ^ 2 - 1)
      ≤ (p * q - 1) * (p * r - 1) * (q * r - 1) := by
  have hp1 : (0 : ℤ) ≤ p ^ 2 - 1 := by nlinarith
  have hq1 : (0 : ℤ) ≤ q ^ 2 - 1 := by nlinarith
  have hr1 : (0 : ℤ) ≤ r ^ 2 - 1 := by nlinarith
  have key := prod_pairs_sub_prod_squares p q r
  nlinarith [mul_nonneg hp1 (sq_nonneg (q - r)),
    mul_nonneg hq1 (sq_nonneg (p - r)),
    mul_nonneg hr1 (sq_nonneg (p - q))]

/-- **Il passo di taglia.** Se `r ^ 2 ≤ 2 * I * (p * q)` con `q < r` e
`0 < 2 * I * p`, allora `r < 2 * I * p`. Applicato a una tripla di `L`, con
`I` l'indice di `5` modulo il fattore massimo, dà `r < 2 * I_r * p`: il
rapporto fra il fattore massimo e il minimo è limitato dall'indice.
@isnad1 id=lt.3h4v.s6.d92953d7bbda from=translated src=- shape=92fca576 vocab=2a3f5b88
-/
theorem lt_two_mul_of_sq_le {p q r I : ℕ} (hIp : 0 < 2 * I * p)
    (hqr : q < r) (h : r ^ 2 ≤ 2 * I * (p * q)) : r < 2 * I * p := by
  have h1 : r * r ≤ 2 * I * p * q := by
    calc r * r = r ^ 2 := (sq r).symm
      _ ≤ 2 * I * (p * q) := h
      _ = 2 * I * p * q := by ring
  have h2 : 2 * I * p * q < 2 * I * p * r := by
    exact mul_lt_mul_of_pos_left hqr hIp
  have hrr : r * r < 2 * I * p * r := lt_of_le_of_lt h1 h2
  exact Nat.lt_of_mul_lt_mul_right hrr

end AgrawalCore
