/-
Nucleo Lean della campagna Agrawal (S45): il criterio di Korselt.
Mathlib non ha né i numeri di Carmichael né quelli di Lucas-Carmichael
(ha solo `Nat.FermatPsp`, lo pseudoprimo di Fermat a base fissata, e
`Nat.ArithmeticFunction.carmichaelFunction`, che è la funzione λ di
Carmichael — un oggetto diverso). Qui si definiscono entrambi via il
criterio di Korselt:
  · `IsCarmichael`        : n squarefree, composito, con (p−1) ∣ (n−1)
                            per ogni fattore primo p
  · `IsLucasCarmichael`   : la variante con (p+1) ∣ (n+1)
e si certificano:
  · `IsCarmichael.odd`, `IsLucasCarmichael.odd` : sono sempre dispari
    (se fossero pari avrebbero un fattore primo dispari q con q−1
    (risp. q+1) pari che dovrebbe dividere n∓1 dispari — assurdo)
  · le proiezioni banali (`not_prime`, `one_lt`, `squarefree`, `korselt`)
  · `korselt_local`       : il passo locale del criterio, via Fermat
  · `IsCarmichael.fermatPsp` : **il criterio di Korselt vero e proprio**,
    n di Carmichael ⟹ n è pseudoprimo di Fermat rispetto a OGNI base
    coprima con n (non solo la base 5 dell'ombra di Fermat già
    certificata in FermatShadow.lean). La colla è la stessa: Fermat
    locale su ogni fattore primo + `Squarefree` per incollare via CRT
    (`Nat.prod_primeFactors_of_squarefree` + `Finset.prod_primes_dvd`).
Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.Seed.Data.Nat.Squarefree
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.Algebra.BigOperators.Associated
import Tengoku.Seed.Tactic.NormNum.Prime
import Tengoku.Seed.NumberTheory.FermatPsp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- Criterio di Korselt: `n` è di Carmichael. `n` è composito,
squarefree, e ogni fattore primo `p` di `n` soddisfa `(p−1) ∣ (n−1)`.-/
def IsCarmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ Squarefree n ∧ ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1)

/-- Numero di Lucas-Carmichael: la variante con `(p+1) ∣ (n+1)`.-/
def IsLucasCarmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ Squarefree n ∧ ∀ p ∈ n.primeFactors, (p + 1) ∣ (n + 1)

/-! ### Proiezioni banali -/

theorem IsCarmichael.not_prime {n : ℕ} (h : IsCarmichael n) : ¬ n.Prime := h.1

theorem IsCarmichael.one_lt {n : ℕ} (h : IsCarmichael n) : 1 < n := h.2.1

theorem IsCarmichael.squarefree {n : ℕ} (h : IsCarmichael n) : Squarefree n := h.2.2.1

theorem IsCarmichael.korselt {n : ℕ} (h : IsCarmichael n) :
    ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1) := h.2.2.2

theorem IsLucasCarmichael.not_prime {n : ℕ} (h : IsLucasCarmichael n) : ¬ n.Prime := h.1

theorem IsLucasCarmichael.one_lt {n : ℕ} (h : IsLucasCarmichael n) : 1 < n := h.2.1

theorem IsLucasCarmichael.squarefree {n : ℕ} (h : IsLucasCarmichael n) : Squarefree n :=
  h.2.2.1

theorem IsLucasCarmichael.korselt {n : ℕ} (h : IsLucasCarmichael n) :
    ∀ p ∈ n.primeFactors, (p + 1) ∣ (n + 1) := h.2.2.2

/-! ### Parità -/

/-- Se `n` è composito, squarefree e pari, ha un fattore primo
dispari `q` (basta prendere un fattore primo di `n / 2`, che non può
essere `2` altrimenti `4 ∣ n` contraddirebbe `Squarefree`).-/
private lemma exists_odd_prime_factor {n : ℕ} (hnp : ¬ n.Prime) (hn1 : 1 < n)
    (hsf : Squarefree n) (heven : (2 : ℕ) ∣ n) :
    ∃ q, q.Prime ∧ q ∣ n ∧ Odd q := by
  obtain ⟨m, hm⟩ := heven
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    omega
  have hm1 : m ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hm
    rw [hm] at hnp
    exact hnp Nat.prime_two
  obtain ⟨q, hqp, hqm⟩ := Nat.exists_prime_and_dvd hm1
  have hqn : q ∣ n := by
    rw [hm]
    exact hqm.mul_left 2
  have hq2 : q ≠ 2 := by
    intro hq2
    subst hq2
    obtain ⟨m', hm'⟩ := hqm
    have h4 : (2 * 2 : ℕ) ∣ n := ⟨m', by rw [hm, hm']; ring⟩
    have hunit := hsf 2 h4
    have h21 : (2 : ℕ) = 1 := Nat.isUnit_iff.mp hunit
    exact absurd h21 (by norm_num)
  exact ⟨q, hqp, hqn, hqp.odd_of_ne_two hq2⟩

/-- **I numeri di Carmichael sono dispari.** Se `n` fosse pari,
avrebbe un fattore primo dispari `q` con `q−1` pari che dovrebbe
dividere `n−1` (dispari, perché `n` è pari): assurdo.-/
theorem IsCarmichael.odd {n : ℕ} (h : IsCarmichael n) : Odd n := by
  have hn1 : 1 < n := h.one_lt
  rcases Nat.even_or_odd n with hn | hn
  · exfalso
    have hdvd2n : (2 : ℕ) ∣ n := hn.two_dvd
    obtain ⟨q, hqp, hqn, hqodd⟩ :=
      exists_odd_prime_factor h.not_prime hn1 h.squarefree hdvd2n
    have hmem : q ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hqn, by omega⟩
    have hdvd := h.korselt q hmem
    have hq1 : (2 : ℕ) ∣ (q - 1) := by
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k, by omega⟩
    have h2dvd : (2 : ℕ) ∣ (n - 1) := dvd_trans hq1 hdvd
    obtain ⟨c, hc⟩ := hn
    obtain ⟨d, hd⟩ := h2dvd
    omega
  · exact hn

/-- **I numeri di Lucas-Carmichael sono dispari.** Stessa dicotomia,
con `q+1` (pari) che dividerebbe `n+1` (dispari se `n` è pari):
assurdo.-/
theorem IsLucasCarmichael.odd {n : ℕ} (h : IsLucasCarmichael n) : Odd n := by
  have hn1 : 1 < n := h.one_lt
  rcases Nat.even_or_odd n with hn | hn
  · exfalso
    have hdvd2n : (2 : ℕ) ∣ n := hn.two_dvd
    obtain ⟨q, hqp, hqn, hqodd⟩ :=
      exists_odd_prime_factor h.not_prime hn1 h.squarefree hdvd2n
    have hmem : q ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hqn, by omega⟩
    have hdvd := h.korselt q hmem
    have hq1 : (2 : ℕ) ∣ (q + 1) := by
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k + 1, by omega⟩
    have h2dvd : (2 : ℕ) ∣ (n + 1) := dvd_trans hq1 hdvd
    obtain ⟨c, hc⟩ := hn
    obtain ⟨d, hd⟩ := h2dvd
    omega
  · exact hn

/-! ### Il criterio di Korselt vero e proprio -/

/-- **Passo locale del criterio di Korselt**: se `p` è primo, `p ∣ n`,
`n` e `b` sono coprimi (quindi anche `p` e `b`), e vale la condizione
di Korselt `(p−1) ∣ (n−1)`, allora `b^(n−1) ≡ 1` in `ZMod p` — via il
piccolo teorema di Fermat su `p`.-/
theorem korselt_local {n p b : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hb : Nat.Coprime n b) (hpk : (p - 1) ∣ (n - 1)) :
    (b : ZMod p) ^ (n - 1) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbp : Nat.Coprime p b := Nat.Coprime.coprime_dvd_left hpn hb
  have hpb : ¬ p ∣ b := hp.coprime_iff_not_dvd.mp hbp
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    exact hpb
  obtain ⟨k, hk⟩ := hpk
  rw [hk, pow_mul, ZMod.pow_card_sub_one_eq_one hb0, one_pow]

/-- **Il criterio di Korselt**: ogni numero di Carmichael è uno
pseudoprimo di Fermat rispetto a OGNI base coprima con esso (non solo
la base 5 dell'ombra di Fermat di `FermatShadow.lean`). La condizione
`(p−1) ∣ (n−1)` dà Fermat locale su ogni fattore primo
(`korselt_local`); `Squarefree n` incolla i fattori via
`Nat.prod_primeFactors_of_squarefree` e `Finset.prod_primes_dvd`.-/
theorem IsCarmichael.fermatPsp {n : ℕ} (h : IsCarmichael n) {b : ℕ}
    (hb : Nat.Coprime n b) : Nat.FermatPsp n b := by
  have hn1 : 1 < n := h.one_lt
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hb
    omega
  refine ⟨?_, h.not_prime, hn1⟩
  show n ∣ b ^ (n - 1) - 1
  have key : ∀ p ∈ n.primeFactors, p ∣ b ^ (n - 1) - 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpk : (p - 1) ∣ (n - 1) := h.korselt p hp
    haveI : Fact p.Prime := ⟨hpp⟩
    have hloc := korselt_local hpp hpn hb hpk
    have hge : 1 ≤ b ^ (n - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
    have h1 : ((b ^ (n - 1) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hge]
      push_cast
      rw [hloc]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp h1
  have hprod := Nat.prod_primeFactors_of_squarefree h.squarefree
  have hprod_dvd :
      (∏ p ∈ n.primeFactors, p) ∣ b ^ (n - 1) - 1 :=
    Finset.prod_primes_dvd (b ^ (n - 1) - 1)
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime) key
  simpa only [hprod] using hprod_dvd

end AgrawalCore
