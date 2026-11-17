/-
Nucleo Lean della campagna Agrawal — lotto 16: LA PROPOSIZIONE DI LENSTRA.

L'enunciato che Lenstra e Pomerance formularono nelle note AIM del 2003
(*Remarks on Agrawal's conjecture*, pp. 30-32) e che da allora è citato in
letteratura — OEIS A329223, la voce enciclopedica sulla congettura, i lavori
di Popovych 2009 e Hegde-Devaraj 2021 — senza essere mai stato verificato
meccanicamente.

  Sia n = p_1 ... p_k con primi distinti. Se
    (1) k ≡ 1 (mod 4),
    (2) p_i ≡ 3 (mod 80) per ogni i,
    (3) (p_i − 1) ∣ (n − 1)      [Carmichael],
    (4) (p_i + 1) ∣ (n + 1)      [Lucas–Carmichael],
  allora  (X−1)^n ≡ X^n − 1  (mod n, X^5 − 1)  e  n² ≢ 1 (mod 5).

La seconda conclusione è ciò che rende un tale n un controesempio genuino:
la congettura di Agrawal ammette l'eccezione n² ≡ 1 (mod r), e qui è esclusa.

La catena dei lotti:
  · classe di n           `prod_class_mod_eighty`   (lotto Korselt/ClassMod80)
  · n ≡ p mod 10(p²−1)    `sub_dvd_of_korselt`      (lotto LcmIdentity)
  · ordine di ζ−1         `order_bounded`           (lotto 12)
  · cuore ciclotomico     `lenstra_local`           (lotto 13)
  · incollaggio locale    `agrawal_mod_p`           (lotto 14)
  · locale → globale      `congruence_of_local`     (lotto GlobalGlue)
  · scappatoia chiusa     `sq_not_one_mod_five`     (lotto ClassMod80)

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.LenstraProp
import Tengoku.AgrawalR5.AgrawalCore.GlobalGlue
import Tengoku.AgrawalR5.AgrawalCore.ClassMod80
import Tengoku.AgrawalR5.AgrawalCore.Korselt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- **LA PROPOSIZIONE DI LENSTRA.**
Se `n` è squarefree, ogni suo fattore primo è `≡ 3 (mod 80)`, la sua classe è
`n ≡ 3 (mod 80)`, e valgono le due condizioni di Korselt, allora la congruenza
di Agrawal a `r = 5` vale modulo `n`, e `n² ≢ 1 (mod 5)`: un tale `n`, se
composto, è un controesempio alla congettura di Agrawal.

La classe `n ≡ 3 (mod 80)` non è un'ipotesi indipendente: segue da
`prod_class_mod_eighty` quando i fattori sono `≡ 3 (mod 80)` e il loro numero
è `≡ 1 (mod 4)`.
@isnad1 id=and.6h1v.s9.2cf47714c387 from=translated src=- shape=3bf34430 vocab=14762092
-/
theorem lenstra_proposition {n : ℕ} (hsq : Squarefree n) (hn0 : 0 < n)
    (hn80 : n % 80 = 3)
    (hfact : ∀ p ∈ n.primeFactors, p % 80 = 3)
    (hcar : ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1))
    (hluc : ∀ p ∈ n.primeFactors, (p + 1) ∣ (n + 1)) :
    (∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g) ∧ n ^ 2 % 5 ≠ 1 := by
  refine ⟨congruence_of_local hsq hn0 ?_, sq_not_one_mod_five hn80⟩
  intro p hp
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hp80 : p % 80 = 3 := hfact p hp
  have hp3 : 3 ≤ p := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hpn : p ≤ n := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
  exact lenstra_congruence_mod_p hp80 hp3 hpn hn0 (hcar p hp) (hluc p hp) hn80

/-- Forma con le ipotesi nella veste originale: `k ≡ 1 (mod 4)` fattori primi
tutti `≡ 3 (mod 80)`, più le due condizioni di Korselt. La classe di `n` viene
dedotta invece che assunta.
@isnad1 id=and.6h1v.s9.cf4fa60eb3ce from=translated src=- shape=54e21a23 vocab=e6e9c796
-/
theorem lenstra_proposition_of_card {n : ℕ} (hsq : Squarefree n) (hn0 : 0 < n)
    (hn80 : n % 80 = 3)
    (hcarm : IsCarmichael n) (hlucas : IsLucasCarmichael n)
    (hfact : ∀ p ∈ n.primeFactors, p % 80 = 3) :
    (∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g) ∧ n ^ 2 % 5 ≠ 1 :=
  lenstra_proposition hsq hn0 hn80 hfact hcarm.korselt hlucas.korselt

end AgrawalCore
