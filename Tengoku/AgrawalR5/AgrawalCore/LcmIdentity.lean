/-
Nucleo Lean della campagna Agrawal — l'aritmetica del lcm che serve a
incastrare le ipotesi della proposizione di Lenstra.

Il fatto centrale, per `p` primo con `p ≡ 3 (mod 80)`:
    lcm(lcm(p−1, p+1), 80) = 10·(p²−1) .
La via è quella diretta, tutta per addizione (niente valutazioni 2-adiche
o 5-adiche): si scrive `p = 80t+3`, da cui
    p − 1 = 2·(40t+1),   p + 1 = 2·(40t+2) ,
due multipli di `2` per interi CONSECUTIVI (`40t+1` e `40t+2`), quindi
`gcd(p−1, p+1) = 2` e `lcm(p−1, p+1) = (p²−1)/2 = 4m`, dove
    p² − 1 = 8m ,   m := 800t² + 60t + 1 .
Il punto chiave è che `m ≡ 1 (mod 20)` SEMPRE (i coefficienti 800 e 60
sono entrambi multipli di 20), quindi `m` è coprimo con `20`, e allora
`lcm(4m, 80) = lcm(4m, 4·20) = 4·lcm(m,20) = 4·20·m = 80·m = 10·(p²−1)`.

Dichiarazioni di questo modulo:
  · `lcm_three_eq`       : il risultato principale, l'identità del lcm
  · `sub_dvd_of_korselt`  : il corollario che serve davvero — se `n` soddisfa
    le due condizioni di Korselt rispetto a `p` (Carmichael e
    Lucas–Carmichael) e la stessa classe `n ≡ 3 (mod 80)`, allora
    `10·(p²−1) ∣ (n−p)`. Si ottiene incollando via `Nat.lcm_dvd`:
    `p−1 ∣ n−p` (da `p−1 ∣ n−1` e `p−1 ∣ p−1`), `p+1 ∣ n−p` (simile),
    e `80 ∣ n−p` (da `n ≡ p (mod 80)`, entrambi in classe 3).
Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.Seed.Data.Nat.GCD.Basic
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- **L'identità del lcm.** Per `p` primo con `p ≡ 3 (mod 80)`,
`lcm(lcm(p−1, p+1), 80) = 10·(p²−1)`. Dimostrazione tutta per addizione:
si scrive `p = 80t+3`, si isola `m = 800t²+60t+1` (con `p²−1 = 8m`), si
usa `gcd(p−1,p+1) = 2` (due multipli di 2 consecutivi) per ottenere
`lcm(p−1,p+1) = 4m`, e `m ≡ 1 (mod 20)` (sempre, perché 800 e 60 sono
multipli di 20) per ottenere `lcm(4m, 80) = 80m = 10(p²−1)`.
@isnad1 id=eq.2h1v.s6.20c27a78e893 from=translated src=- shape=f3a86c92 vocab=9132f5e7
-/
theorem lcm_three_eq {p : ℕ} (hp : p % 80 = 3) (_hp3 : 3 ≤ p) :
    Nat.lcm (Nat.lcm (p - 1) (p + 1)) 80 = 10 * (p * p - 1) := by
  obtain ⟨t, hpt⟩ : ∃ t, p = 80 * t + 3 := ⟨p / 80, by omega⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = 800 * (t * t) + 60 * t + 1 := ⟨_, rfl⟩
  -- le identità che coinvolgono `t·t` si stabiliscono subito, finché
  -- la definizione di `m` è ancora in scope
  have hpm : p * p = 8 * m + 1 := by rw [hpt, hm_def]; ring
  have h1 : p - 1 = 2 * (40 * t + 1) := by omega
  have h2 : p + 1 = 2 * (40 * t + 1 + 1) := by omega
  have hprod : (p - 1) * (p + 1) = 8 * m := by rw [h1, h2, hm_def]; ring
  have hm20 : m % 20 = 1 := by
    rw [hm_def]; generalize t * t = u; omega
  -- da qui in poi `m` e `t` sono opachi: niente più termini non lineari,
  -- `omega` può lavorare in sicurezza
  clear hm_def hpt
  have hgcd12 : Nat.gcd (p - 1) (p + 1) = 2 := by
    rw [h1, h2, Nat.gcd_mul_left]
    have hcop : Nat.gcd (40 * t + 1) (40 * t + 1 + 1) = 1 :=
      (Nat.coprime_self_add_right (m := 40 * t + 1) (n := 1)).mpr (by simp)
    rw [hcop]
  have hL : Nat.gcd (p - 1) (p + 1) * Nat.lcm (p - 1) (p + 1) = (p - 1) * (p + 1) :=
    Nat.gcd_mul_lcm _ _
  rw [hgcd12, hprod] at hL
  have hlcm12 : Nat.lcm (p - 1) (p + 1) = 4 * m := by omega
  rw [hlcm12]
  have hcopm20 : Nat.Coprime m 20 := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm, Nat.gcd_rec, hm20]
    decide
  have h80eq : (80 : ℕ) = 4 * 20 := by norm_num
  have hgcd420 : Nat.gcd (4 * m) 80 = 4 := by
    rw [h80eq, Nat.gcd_mul_left, hcopm20]
  have hL2 : Nat.gcd (4 * m) 80 * Nat.lcm (4 * m) 80 = (4 * m) * 80 :=
    Nat.gcd_mul_lcm _ _
  rw [hgcd420] at hL2
  have hlcm2 : Nat.lcm (4 * m) 80 = 80 * m := by omega
  rw [hlcm2]
  omega

/-- **Il corollario che serve davvero.** Se `n` soddisfa le due condizioni
di Korselt rispetto a `p` — `(p−1) ∣ (n−1)` (Carmichael) e `(p+1) ∣ (n+1)`
(Lucas–Carmichael) — ed è nella stessa classe `n ≡ 3 (mod 80)` di `p`,
allora `10·(p²−1)` divide lo scarto `n − p`. Ciascuno dei tre moduli
`p−1`, `p+1`, `80` divide separatamente `n−p` (perché divide sia il
"più uno" che il "meno uno" corrispondente, o perché `n` e `p` cadono
nella stessa classe mod 80); il loro lcm — che è `10(p²−1)` per
`lcm_three_eq` — divide dunque anch'esso `n−p`.
@isnad1 id=dvd.6h2v.s7.c742df361f1f from=translated src=- shape=2934682d vocab=971a9c0f
-/
theorem sub_dvd_of_korselt {p n : ℕ} (hp : p % 80 = 3) (hp3 : 3 ≤ p) (hpn : p ≤ n)
    (h1 : (p - 1) ∣ (n - 1)) (h2 : (p + 1) ∣ (n + 1)) (h80 : n % 80 = 3) :
    (10 * (p * p - 1)) ∣ (n - p) := by
  have hA : (p - 1) ∣ (n - p) := by
    have hd := Nat.dvd_sub h1 (dvd_refl (p - 1))
    have heq : (n - 1) - (p - 1) = n - p := by omega
    rwa [heq] at hd
  have hB : (p + 1) ∣ (n - p) := by
    have hd := Nat.dvd_sub h2 (dvd_refl (p + 1))
    have heq : (n + 1) - (p + 1) = n - p := by omega
    rwa [heq] at hd
  have hC : (80 : ℕ) ∣ (n - p) := by
    have hcong : p ≡ n [MOD 80] := by unfold Nat.ModEq; omega
    exact (Nat.modEq_iff_dvd' hpn).mp hcong
  have hlcm1 : Nat.lcm (p - 1) (p + 1) ∣ (n - p) := Nat.lcm_dvd hA hB
  have hlcm2 : Nat.lcm (Nat.lcm (p - 1) (p + 1)) 80 ∣ (n - p) := Nat.lcm_dvd hlcm1 hC
  rwa [lcm_three_eq hp hp3] at hlcm2

end AgrawalCore
