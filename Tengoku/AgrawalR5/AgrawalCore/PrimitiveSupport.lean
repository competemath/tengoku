/-
Kernel aritmetico della riduzione H4 a quattro coefficienti.

Il teorema algebrico esterno identifica, fuori dai primi cattivi, il
supporto originale con la divisibilità simultanea di quattro interi.
Questo modulo formalizza:

* la compressione esatta dei quattro coefficienti in un solo gcd;
* il trasporto del supporto attraverso tale compressione;
* il nucleo aritmetico dell'esclusione della famiglia
  `p - 1 = 8 * q^e`: se due semiordini coprimi dividono la stessa
  quantità con un solo primo dispari, almeno uno dei due ordini
  completi divide `8`.

Non formalizza ancora la valutazione di `Φₘ(γ)` nell'anello quadratico:
quello è il nuovo confine algebrico esplicito.
-/
import Tengoku.Seed.Data.Nat.GCD.Basic
import Tengoku.Seed.Data.Nat.Prime.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- Il gcd dei quattro coefficienti integrali della riduzione primitiva.-/
def fourCoefficientGcd (c d a w : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd c d) (Nat.gcd a w)

/-- Un primo (o qualunque naturale) divide il gcd a quattro coefficienti
se e solo se divide ciascun coefficiente.-/
theorem dvd_fourCoefficientGcd_iff {t c d a w : ℕ} :
    t ∣ fourCoefficientGcd c d a w ↔
      t ∣ c ∧ t ∣ d ∧ t ∣ a ∧ t ∣ w := by
  rw [fourCoefficientGcd, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff,
    Nat.dvd_gcd_iff]
  aesop

/-- Interfaccia kernel-pura del teorema del supporto: una volta provata
la divisibilità simultanea dei quattro coefficienti, la formulazione
mediante il singolo intero `D` è esattamente equivalente.-/
theorem primitiveSupport_iff_fourCoefficientGcd {p G c d a w : ℕ}
    (hcoeff :
      p ∣ G ↔ p ∣ c ∧ p ∣ d ∧ p ∣ a ∧ p ∣ w) :
    p ∣ G ↔ p ∣ fourCoefficientGcd c d a w := by
  rw [hcoeff, dvd_fourCoefficientGcd_iff]

/-- Se due semiordini coprimi dividono `4*q^e`, almeno uno dei due
divide già `4`. È il nucleo della regione esclusa `p-1 = 8*q^e`.-/
theorem one_semiorder_dvd_four_of_single_odd_prime
    {q e r s : ℕ} (hq : q.Prime) (hrs : Nat.Coprime r s)
    (hr : r ∣ 4 * q ^ e) (hs : s ∣ 4 * q ^ e) :
    r ∣ 4 ∨ s ∣ 4 := by
  by_cases hqr : q ∣ r
  · right
    have hqns : ¬ q ∣ s := by
      intro hqs
      have hqgcd : q ∣ Nat.gcd r s := Nat.dvd_gcd hqr hqs
      rw [hrs.gcd_eq_one] at hqgcd
      exact hq.not_dvd_one hqgcd
    have hcop : Nat.Coprime s (q ^ e) :=
      hq.coprime_pow_of_not_dvd hqns
    exact hcop.dvd_mul_right.mp hs
  · left
    have hcop : Nat.Coprime r (q ^ e) :=
      hq.coprime_pow_of_not_dvd hqr
    exact hcop.dvd_mul_right.mp hr

/-- Forma sugli ordini completi: se `2r` e `2s` dividono `8*q^e` e
`r,s` sono coprimi, almeno uno dei due ordini divide `8`.-/
theorem one_order_dvd_eight_of_single_odd_prime
    {q e r s : ℕ} (hq : q.Prime) (hrs : Nat.Coprime r s)
    (hR : 2 * r ∣ 8 * q ^ e) (hE : 2 * s ∣ 8 * q ^ e) :
    2 * r ∣ 8 ∨ 2 * s ∣ 8 := by
  have hr : r ∣ 4 * q ^ e := by
    have hR' : 2 * r ∣ 2 * (4 * q ^ e) := by
      simpa only [show (8 : ℕ) = 2 * 4 by norm_num, mul_assoc] using hR
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
    exact hR'
  have hs : s ∣ 4 * q ^ e := by
    have hE' : 2 * s ∣ 2 * (4 * q ^ e) := by
      simpa only [show (8 : ℕ) = 2 * 4 by norm_num, mul_assoc] using hE
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
    exact hE'
  rcases one_semiorder_dvd_four_of_single_odd_prime hq hrs hr hs with
      hr4 | hs4
  · left
    exact Nat.mul_dvd_mul_left 2 hr4
  · right
    exact Nat.mul_dvd_mul_left 2 hs4

/-- General dyadic form of `one_semiorder_dvd_four_of_single_odd_prime`:
if two coprime semiorders divide a number supported on `2` and a single
odd prime `q`, one of them is supported on `2` alone.-/
theorem one_semiorder_dvd_two_power_of_single_odd_prime
    {q e b r s : ℕ} (hq : q.Prime) (hrs : Nat.Coprime r s)
    (hr : r ∣ 2 ^ b * q ^ e) (hs : s ∣ 2 ^ b * q ^ e) :
    r ∣ 2 ^ b ∨ s ∣ 2 ^ b := by
  by_cases hqr : q ∣ r
  · right
    have hqns : ¬q ∣ s := by
      intro hqs
      have hqgcd : q ∣ Nat.gcd r s := Nat.dvd_gcd hqr hqs
      rw [hrs.gcd_eq_one] at hqgcd
      exact hq.not_dvd_one hqgcd
    exact (hq.coprime_pow_of_not_dvd hqns).dvd_mul_right.mp hs
  · left
    exact (hq.coprime_pow_of_not_dvd hqr).dvd_mul_right.mp hr

/-- Complete-order version at arbitrary dyadic depth.  If `2r` and `2s`
divide `2^(b+1) q^e`, one complete order already divides `2^(b+1)`.-/
theorem one_order_dvd_two_pow_succ_of_single_odd_prime
    {q e b r s : ℕ} (hq : q.Prime) (hrs : Nat.Coprime r s)
    (hR : 2 * r ∣ 2 ^ (b + 1) * q ^ e)
    (hE : 2 * s ∣ 2 ^ (b + 1) * q ^ e) :
    2 * r ∣ 2 ^ (b + 1) ∨ 2 * s ∣ 2 ^ (b + 1) := by
  have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by
    rw [pow_succ']
  have hr : r ∣ 2 ^ b * q ^ e := by
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
    simpa only [hpow, mul_assoc] using hR
  have hs : s ∣ 2 ^ b * q ^ e := by
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
    simpa only [hpow, mul_assoc] using hE
  rcases one_semiorder_dvd_two_power_of_single_odd_prime
      hq hrs hr hs with hrTwo | hsTwo
  · left
    simpa only [hpow] using Nat.mul_dvd_mul_left 2 hrTwo
  · right
    simpa only [hpow] using Nat.mul_dvd_mul_left 2 hsTwo

end AgrawalCore
