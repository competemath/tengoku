/-
Nucleo Lean della campagna Agrawal — INGRESSO SQUAREFREE.

Questo modulo formalizza il Lemma di riduzione squarefree usato nel paper:
se `p ∣ n` e la congruenza globale, ridotta modulo `p`, vale con esponente
`n`, allora la vera riga locale vale con esponente `n / p`.

La prova evita di assumere astrattamente che il Frobenius sia iniettivo
nell'anello ciclotomico. Si valuta invece la congruenza in `ζ^a`, dove
`a * p ≡ 1 (mod 5)`. Il Frobenius manda direttamente `ζ^a - 1` in
`ζ - 1`, e quindi cancella il fattore primo dall'esponente.
-/
import Tengoku.AgrawalR5.AgrawalCore.LocalTransport
import Tengoku.AgrawalR5.AgrawalCore.GlobalGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- La congruenza globale di Agrawal per `r = 5`, con il quoziente
polinomiale esibito esplicitamente.-/
def AgrawalCongruenceFive (n : ℕ) : Prop :=
  ∃ g : Polynomial (ZMod n),
    (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g

/-- Se la congruenza modulo `p` vale con esponente `p * m` e `p ≠ 5`,
allora la riga ciclotomica locale vale con esponente `m`.

La scelta di `a ∈ {1,2,3,4}` con `a*p ≡ 1 (mod 5)` rende la discesa
completamente esplicita e non richiede una decomposizione in campi.-/
theorem localS5_of_prime_multiple {m : ℕ} (hp5 : p ≠ 5)
    (h : ∃ g : Polynomial (ZMod p),
      (X - 1) ^ (p * m) = X ^ (p * m) - 1 + (X ^ 5 - 1) * g) :
    LocalS5 p m := by
  obtain ⟨g, hg⟩ := h
  have hpmod :
      p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have hne : p % 5 ≠ 0 := by
      intro h0
      have hdiv : 5 ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact hp5
        ((Nat.prime_dvd_prime_iff_eq (by norm_num) Fact.out).mp hdiv).symm
    omega
  have descend (a : ℕ) (hap : (a * p) % 5 = 1) : LocalS5 p m := by
    have heval := congrArg
      (Polynomial.aeval ((zeta5 : Phi5Ring p) ^ a)) hg
    simp only [map_add, map_sub, map_mul, map_pow, map_one,
      Polynomial.aeval_X] at heval
    have ha5 : (((zeta5 : Phi5Ring p) ^ a) ^ 5) = 1 := by
      rw [← pow_mul, mul_comm a 5, pow_mul, zeta5_pow_five, one_pow]
    rw [ha5, sub_self, zero_mul, add_zero] at heval
    have hfrob : (((zeta5 : Phi5Ring p) ^ a) - 1) ^ p = zeta5 - 1 := by
      rw [sub_pow_char, one_pow, ← pow_mul, zeta5_pow_mod, hap, pow_one]
    have hamod : (a * (p * m)) % 5 = m % 5 := by
      rw [← Nat.mul_assoc, Nat.mul_mod, hap, one_mul, Nat.mod_mod]
    calc
      ((zeta5 : Phi5Ring p) - 1) ^ m
          = ((((zeta5 : Phi5Ring p) ^ a) - 1) ^ p) ^ m := by rw [hfrob]
      _ = (((zeta5 : Phi5Ring p) ^ a) - 1) ^ (p * m) := by rw [pow_mul]
      _ = ((zeta5 : Phi5Ring p) ^ a) ^ (p * m) - 1 := heval
      _ = zeta5 ^ (a * (p * m)) - 1 := by
        rw [← pow_mul]
      _ = zeta5 ^ m - 1 := by
        congr 1
        calc
          (zeta5 : Phi5Ring p) ^ (a * (p * m))
              = zeta5 ^ ((a * (p * m)) % 5) := zeta5_pow_mod _
          _ = zeta5 ^ (m % 5) := by rw [hamod]
          _ = zeta5 ^ m := (zeta5_pow_mod m).symm
  rcases hpmod with hp | hp | hp | hp
  · apply descend 1
    simpa using hp
  · apply descend 3
    rw [Nat.mul_mod, hp]
  · apply descend 2
    rw [Nat.mul_mod, hp]
  · apply descend 4
    rw [Nat.mul_mod, hp]

/-- La riga locale con esponente `m` si solleva all'esponente `p*m`
mediante Frobenius. Questa è la direzione inversa della discesa esplicita.-/
theorem localS5_prime_multiple {m : ℕ} (h : LocalS5 p m) :
    LocalS5 p (p * m) := by
  calc
    ((zeta5 : Phi5Ring p) - 1) ^ (p * m)
        = (((zeta5 : Phi5Ring p) - 1) ^ m) ^ p := by
          rw [← pow_mul, Nat.mul_comm]
    _ = (zeta5 ^ m - 1) ^ p := by rw [h]
    _ = (zeta5 ^ m) ^ p - 1 := by rw [sub_pow_char, one_pow]
    _ = zeta5 ^ (p * m) - 1 := by rw [← pow_mul, Nat.mul_comm]

/-- La congruenza globale, ridotta modulo un fattore primo `p ∣ n`, produce
la riga locale con il quoziente esatto `n / p`. Questa è la direzione
globale-verso-locale del lemma di riduzione squarefree; la squarefreeness
serve successivamente per ricomporre tutti i fattori, non in questa singola
discesa.-/
theorem localS5_of_global_factor {n : ℕ} (hp5 : p ≠ 5) (hpdvd : p ∣ n)
    (h : AgrawalCongruenceFive n) :
    LocalS5 p (n / p) := by
  obtain ⟨g, hg⟩ := h
  have hmap := congrArg (Polynomial.map (ZMod.castHom hpdvd (ZMod p))) hg
  simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_one, Polynomial.map_X] at hmap
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
  apply localS5_of_prime_multiple (p := p) hp5
  refine ⟨g.map (ZMod.castHom hpdvd (ZMod p)), ?_⟩
  simpa [hmul] using hmap

/-- **LEMMA DI RIDUZIONE SQUAREFREE, `r = 5`, kernel-puro.**

Per `n` squarefree e non divisibile per `5`, la congruenza globale è
equivalente alle righe locali con gli esponenti complementari `n / p`.
Questa è l'interfaccia aritmetica usata dal teorema di struttura globale.-/
theorem squarefree_ingress_iff {n : ℕ} (hsq : Squarefree n) (hn : 0 < n)
    (h5 : ¬ 5 ∣ n) :
    AgrawalCongruenceFive n ↔
      ∀ p (hp : p ∈ n.primeFactors),
        @LocalS5 p (n / p) ⟨Nat.prime_of_mem_primeFactors hp⟩ := by
  constructor
  · intro h p hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp5 : p ≠ 5 := by
      intro hpeq
      exact h5 (hpeq ▸ hpdvd)
    exact @localS5_of_global_factor p
      ⟨Nat.prime_of_mem_primeFactors hp⟩ n hp5 hpdvd h
  · intro hlocal
    apply congruence_of_local hsq hn
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp5 : p ≠ 5 := by
      intro hpeq
      exact h5 (hpeq ▸ hpdvd)
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
    have hrow : LocalS5 p (n / p) := hlocal p hp
    have hrow_n : LocalS5 p n := by
      rw [← hmul]
      exact localS5_prime_multiple hrow
    exact agrawal_mod_p hn hp5 hrow_n

end AgrawalCore
