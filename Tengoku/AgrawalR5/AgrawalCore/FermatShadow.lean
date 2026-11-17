/-
Nucleo Lean della campagna Agrawal (S45) — lotto 7: L'OMBRA DI FERMAT.
La colla aritmetica del teorema della dodicesima ondata: se n è
squarefree, 5 ∤ n, e ogni fattore primo p di n soddisfa il vincolo di
norma 5^(n/p − 1) ≡ 1 (mod p), allora n è uno pseudoprimo di Fermat
in base 5: n ∣ 5^(n−1) − 1. Il vincolo di norma per i controesempi di
Agrawal è il teorema della prima notte della campagna; qui entra come
ipotesi, e la catena n−1 = p(m−1)+(p−1) + incollaggio squarefree è
certificata dal kernel. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.Seed.Data.Nat.Squarefree
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.Algebra.BigOperators.Associated
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- Passo locale dell'ombra: per `p ∣ n` primo, `p ≠ 5`, dal vincolo
di norma `5^(n/p − 1) = 1` segue `5^(n−1) = 1` in `ZMod p`.
@isnad1 id=eq.4h2v.s7.dcd0b46bdec3 from=translated src=- shape=15ae2bb4 vocab=ad0fd531
-/
lemma fermat_shadow_local {n p : ℕ} (hp : p.Prime) (hdvd : p ∣ n)
    (hp5 : p ≠ 5) (H : (5 : ZMod p) ^ (n / p - 1) = 1) :
    (5 : ZMod p) ^ (n - 1) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h50 : (5 : ZMod p) ≠ 0 := by
    have h : ((5 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro h
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
    exact_mod_cast h
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h1
    · simp at hm; omega
    · exact h1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hnp : n / p = m' + 1 := by
    rw [hm]
    exact Nat.mul_div_cancel_left _ hp.pos
  have H' : (5 : ZMod p) ^ m' = 1 := by
    rw [hnp] at H
    simpa using H
  have hn2 : n = p * m' + p := by rw [hm]; ring
  have e : n - 1 = p * m' + (p - 1) := by
    have hp1 : 1 ≤ p := hp.pos
    omega
  calc (5 : ZMod p) ^ (n - 1)
      = (5 ^ p) ^ m' * 5 ^ (p - 1) := by rw [e, pow_add, pow_mul]
    _ = 5 ^ m' * 5 ^ (p - 1) := by rw [ZMod.pow_card]
    _ = 1 * 1 := by rw [H', ZMod.pow_card_sub_one_eq_one h50]
    _ = 1 := one_mul 1

/-- **L'ombra di Fermat** (colla aritmetica, certificata): `n`
squarefree con `5 ∤ n` e il vincolo di norma su ogni fattore primo è
uno pseudoprimo di Fermat in base `5`: `n ∣ 5^(n−1) − 1`.
@isnad1 id=dvd.3h1v.s7.53497cc8a056 from=translated src=- shape=9535f079 vocab=7d575c49
-/
theorem fermat_shadow {n : ℕ} (hsq : Squarefree n) (h5 : ¬ (5 ∣ n))
    (H : ∀ p : ℕ, p.Prime → p ∣ n → (5 : ZMod p) ^ (n / p - 1) = 1) :
    n ∣ 5 ^ (n - 1) - 1 := by
  have key : ∀ p ∈ n.primeFactors, p ∣ 5 ^ (n - 1) - 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp5 : p ≠ 5 := fun h => h5 (h ▸ hpd)
    haveI : Fact p.Prime := ⟨hpp⟩
    have hloc := fermat_shadow_local hpp hpd hp5 (H p hpp hpd)
    have hge : 1 ≤ 5 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h1 : ((5 ^ (n - 1) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hge]
      push_cast
      rw [hloc]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp h1
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  have hprod_dvd :
      (∏ p ∈ n.primeFactors, p) ∣ 5 ^ (n - 1) - 1 :=
    Finset.prod_primes_dvd (5 ^ (n - 1) - 1)
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime) key
  simpa only [hprod] using hprod_dvd

end AgrawalCore
