/-
Nucleo Lean della campagna Agrawal — lotto 15: LA PROPOSIZIONE DI LENSTRA,
PARTE LOCALE COMPLETA.

Qui si assembla la catena costruita nei lotti 12-14 e nei moduli laterali:
dalle sole ipotesi di Lenstra su un primo `p` che divide un candidato `n`
si ottiene la congruenza di Agrawal modulo `p`.

  ipotesi di Korselt su p          (p−1 ∣ n−1,  p+1 ∣ n+1)
  + classe             (p ≡ 3 mod 80,  n ≡ 3 mod 80)
    ──[`sub_dvd_of_korselt`, lcm(p−1,p+1,80) = 10(p²−1)]──▶  n ≡ p mod 10(p²−1)
    ──[`lenstra_local`, che usa `order_bounded` del lotto 12]──▶
        (ζ−1)^n = ζ^n − 1  nella componente ciclotomica
    ──[`agrawal_mod_p`, che incolla con la componente banale]──▶
        (X−1)^n = X^n − 1 + (X⁵−1)·g   in  (Z/p)[X]

Il punto di tutta la costruzione, ed è ciò che rende la proposizione vera:
**le tre condizioni imposte a `n` sono soddisfatte anche da `p` stesso**,
quindi `n` e `p` sono congrui modulo il minimo comune multiplo, che coincide
esattamente con il modulo entro cui vive l'ordine di `ζ−1`.

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.LocalGlue
import Tengoku.AgrawalR5.AgrawalCore.LcmIdentity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- **La parte locale della proposizione di Lenstra.**
Sia `p ≡ 3 (mod 80)` un primo e sia `n ≥ p` con `n ≡ 3 (mod 80)` che soddisfa
le due condizioni di Korselt rispetto a `p`. Allora la congruenza di Agrawal a
`r = 5` vale modulo `p`.
@isnad1 id=ex.7h2v.s10.2ed57f350daf from=translated src=- shape=ca69080e vocab=6344d69c
-/
theorem lenstra_congruence_mod_p {n : ℕ} (hp80 : p % 80 = 3) (hp3 : 3 ≤ p)
    (hpn : p ≤ n) (hn0 : 0 < n)
    (hcar : (p - 1) ∣ (n - 1)) (hluc : (p + 1) ∣ (n + 1)) (hn80 : n % 80 = 3) :
    ∃ g : Polynomial (ZMod p),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g := by
  -- p ≠ 5, perché 5 % 80 = 5 ≠ 3
  have hp5 : p ≠ 5 := by
    intro h; rw [h] at hp80; norm_num at hp80
  -- le tre congruenze, soddisfatte anche da p, danno n ≡ p mod 10(p²−1)
  obtain ⟨k, hk⟩ := sub_dvd_of_korselt hp80 hp3 hpn hcar hluc hn80
  have hn : n = p + k * (10 * (p * p - 1)) := by
    have h := (Nat.sub_eq_iff_eq_add hpn).mp hk
    rw [h]; ring
  -- il cuore, poi l'incollaggio
  exact agrawal_mod_p hn0 hp5 (lenstra_local hp80 hp5 hn)

end AgrawalCore
