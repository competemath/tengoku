/-
Nucleo Lean della campagna Agrawal — il ponte tra `Nat.primeFactors` e
`ClassMod80.lean`, che manca alla proposizione di Lenstra così come formalizzata
finora.

La proposizione originale di Lenstra e Pomerance (note AIM 2003) NON assume
`n ≡ 3 (mod 80)`: assume che `n = p_1 ⋯ p_k` con `k` fattori primi distinti,
tutti `≡ 3 (mod 80)`, e con `k ≡ 1 (mod 4)`; e DEDUCE `n ≡ 3 (mod 80)` dal
fatto che `3` ha ordine `4` modulo `80` (`3^4 = 81 ≡ 1`). Il lemma
`prod_class_mod_eighty` di `ClassMod80.lean` fa esattamente questo passo, ma
è enunciato su `List ℕ`, mentre `n.primeFactors` è un `Finset ℕ`. Finché il
ponte tra i due mondi manca, la nostra `lenstra_proposition` (in
`Lenstra.lean`) resta più debole dell'originale: assume `n % 80 = 3` invece
di dedurla dalla cardinalità dei fattori primi.

  · `finset_prod_mod_eighty` : l'analogo per `Finset ℕ` di `prod_mod_eighty`
                                (stessa dimostrazione, per induzione, ma su
                                `Finset.induction_on` invece che su liste)
  · `mod_eighty_of_card`     : il ponte vero e proprio — se `n` è squarefree
                                e i suoi fattori primi sono tutti `≡ 3
                                (mod 80)` in numero `≡ 1 (mod 4)`, allora
                                `n ≡ 3 (mod 80)`. La chiave è
                                `Nat.prod_primeFactors_of_squarefree`, che
                                per `n` squarefree dà `∏ p ∈ n.primeFactors,
                                p = n`.
  · `lenstra_proposition_card` : la proposizione di Lenstra nella sua veste
                                ESATTAMENTE originale (ipotesi su `k` e sui
                                fattori primi, nessuna ipotesi diretta sulla
                                classe di `n`), ottenuta componendo
                                `mod_eighty_of_card` con `lenstra_proposition`.

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.ClassMod80
import Tengoku.AgrawalR5.AgrawalCore.Lenstra
import Tengoku.Seed.Data.Nat.Squarefree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators
open Polynomial

namespace AgrawalCore

/-! ### Il ponte `Finset` -/

/-- **Il prodotto di un `Finset` di classe `3` mod `80`** vale, modulo `80`,
`3` elevato alla cardinalità del `Finset`. Analogo per `Finset ℕ` di
`prod_mod_eighty` (`ClassMod80.lean`), stessa dimostrazione per induzione,
qui su `Finset.induction_on` invece che su liste.-/
private lemma finset_prod_mod_eighty {s : Finset ℕ} (h : ∀ x ∈ s, x % 80 = 3) :
    (∏ p ∈ s, p) % 80 = 3 ^ s.card % 80 := by
  have hmod : (∏ p ∈ s, p) ≡ 3 ^ s.card [MOD 80] := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Nat.ModEq.refl]
    | insert a s ha ih =>
      have haa : a ≡ 3 [MOD 80] := h a (Finset.mem_insert_self a s)
      have hs : (∏ p ∈ s, p) ≡ 3 ^ s.card [MOD 80] :=
        ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      have hstep := haa.mul hs
      simpa [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ'] using hstep
  exact hmod

/-- **IL PONTE.** Se `n` è squarefree, ogni suo fattore primo è `≡ 3
(mod 80)`, e il NUMERO dei fattori primi è `≡ 1 (mod 4)`, allora
`n ≡ 3 (mod 80)`. Questa è esattamente la deduzione che Lenstra e Pomerance
fanno nella loro proposizione originale, a partire dal fatto che `3` ha
ordine `4` modulo `80`: qui non si assume più la classe di `n`, la si
ottiene dalla cardinalità dei fattori.-/
theorem mod_eighty_of_card {n : ℕ} (hsq : Squarefree n) (_hn0 : 0 < n)
    (hfact : ∀ p ∈ n.primeFactors, p % 80 = 3)
    (hcard : n.primeFactors.card % 4 = 1) :
    n % 80 = 3 := by
  have hprod : (∏ p ∈ n.primeFactors, p) = n := Nat.prod_primeFactors_of_squarefree hsq
  have hmod : n % 80 = 3 ^ n.primeFactors.card % 80 := by
    conv_lhs => rw [← hprod]
    exact finset_prod_mod_eighty hfact
  rw [hmod, pow_three_mod_eighty, hcard]
  decide

/-! ### La proposizione di Lenstra, nella veste esattamente originale -/

/-- **LA PROPOSIZIONE DI LENSTRA, forma originale.** Esattamente l'enunciato
di Lenstra e Pomerance: `n` squarefree con `k` fattori primi distinti, tutti
`≡ 3 (mod 80)`, con `k ≡ 1 (mod 4)`, più le due condizioni di Korselt
(Carmichael e Lucas-Carmichael). Nessuna ipotesi diretta sulla classe di
`n`: la si deduce da `mod_eighty_of_card`, poi si applica
`lenstra_proposition`.-/
theorem lenstra_proposition_card {n : ℕ} (hsq : Squarefree n) (hn0 : 0 < n)
    (hfact : ∀ p ∈ n.primeFactors, p % 80 = 3)
    (hcard : n.primeFactors.card % 4 = 1)
    (hcar : ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1))
    (hluc : ∀ p ∈ n.primeFactors, (p + 1) ∣ (n + 1)) :
    (∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g)
      ∧ n ^ 2 % 5 ≠ 1 :=
  lenstra_proposition hsq hn0 (mod_eighty_of_card hsq hn0 hfact hcard) hfact hcar hluc

end AgrawalCore
