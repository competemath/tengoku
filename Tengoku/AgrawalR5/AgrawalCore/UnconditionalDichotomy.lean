/-
Nucleo Lean della campagna Agrawal — DICOTOMIA LOGICA DEI DUE TESTIMONI.

Questo modulo separa i due muri rimasti nel montaggio squarefree a r = 5.
Il passaggio dal candidato globale allo scheletro quartico è ora interamente
nel kernel:

  candidato -> testimone locale H4
             oppure scheletro inerte, cardinalità dispari >= 3.

In questo modulo il passaggio successivo dallo scheletro a una nozione
arbitraria di fibra resta la premessa parametrica `SkeletonToFiber`.
`ExplicitFiber.lean` la istanzia poi, senza assiomi, con i due risultanti
terminali concreti. Nessun modulo afferma H4 o la vacuità universale delle
fibre.

Campagna UNICO, 27 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.TwoFactorIngress

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- Un candidato squarefree non banale alla conclusione `n² ≡ 1 (mod 5)`.
Questa definizione non afferma che un simile candidato esista.-/
def SquarefreeCounterexampleCandidate (n : ℕ) : Prop :=
  Squarefree n
    ∧ (¬ n.Prime)
    ∧ (¬ ((5 : ℕ) ∣ n))
    ∧ AgrawalCongruenceFive n
    ∧ (n ^ 2 % 5 ≠ 1)

/-- If a number is prime to `5` but its square is not `1 mod 5`, then its
residue is one of the two inert classes `2,3 mod 5`.-/
theorem inertModFive_of_square_ne_one {n : ℕ}
    (h5 : ¬ 5 ∣ n) (hbad : n ^ 2 % 5 ≠ 1) :
    InertModFive n := by
  have h0 : n % 5 ≠ 0 := by
    exact fun hn0 => h5 (Nat.dvd_of_mod_eq_zero hn0)
  have hlt : n % 5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases hn : n % 5 <;>
    simp [InertModFive, hn, Nat.pow_mod] at h0 hbad ⊢

/-- Dividing an inert residue by a split residue preserves inertness.
The statement is written for exact natural-number division because this
is the form used by complementary local exponents.-/
theorem inertModFive_div_of_splitModFive {n p : ℕ}
    (hpdvd : p ∣ n) (hp : SplitModFive p) (hn : InertModFive n) :
    InertModFive (n / p) := by
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
  have hmod := congrArg (fun x : ℕ => x % 5) hmul
  have hlt : (n / p) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases hp with hp1 | hp4
  · rcases hn with hn2 | hn3
    · left
      simpa [Nat.mul_mod, hp1, hn2] using hmod
    · right
      simpa [Nat.mul_mod, hp1, hn3] using hmod
  · rcases hn with hn2 | hn3
    · interval_cases hq : (n / p) % 5 <;>
        simp [InertModFive, Nat.mul_mod, hp4, hn2, hq] at hmod ⊢
    · interval_cases hq : (n / p) % 5 <;>
        simp [InertModFive, Nat.mul_mod, hp4, hn3, hq] at hmod ⊢

/-- **Concrete quartic skeleton.**

Every prime factor is inert in `Q(√5)` and carries the literal local row
with complementary exponent `n/p`.  This is the exact kernel-level output
of the global ingress once split order-four witnesses have been excluded.-/
def QuarticSkeleton (n : ℕ) : Prop :=
  ∀ p (hp : p ∈ n.primeFactors),
    InertModFive p
      ∧ @LocalS5 p (n / p) ⟨Nat.prime_of_mem_primeFactors hp⟩

/-- The square of a product of inert residues is `4^card` modulo `5`.-/
private lemma finset_inert_product_sq_mod_five {s : Finset ℕ}
    (h : ∀ p ∈ s, InertModFive p) :
    (∏ p ∈ s, p) ^ 2 % 5 = 4 ^ s.card % 5 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haInert := h a (Finset.mem_insert_self a s)
      have haSq : a ^ 2 % 5 = 4 := by
        rcases haInert with ha2 | ha3
        · simp [Nat.pow_mod, ha2]
        · simp [Nat.pow_mod, ha3]
      have ih' := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
      simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      rw [Nat.mul_pow, Nat.mul_mod, haSq, ih']
      simp [pow_succ', Nat.mul_mod]

/-- In the quartic skeleton, a candidate violating `n² = 1 mod 5` has an
odd number of prime factors.  This is the cardinality part of the
mod-`5` structure theorem.-/
theorem quarticSkeleton_card_odd {n : ℕ}
    (hn : SquarefreeCounterexampleCandidate n) (hskeleton : QuarticSkeleton n) :
    Odd n.primeFactors.card := by
  rcases hn with ⟨hsq, _hnprime, _h5, _hglobal, hbad⟩
  apply Nat.not_even_iff_odd.mp
  intro heven
  rcases heven with ⟨k, hk⟩
  have hprod : (∏ p ∈ n.primeFactors, p) = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hsquareProduct :
      (∏ p ∈ n.primeFactors, p) ^ 2 % 5 =
        4 ^ n.primeFactors.card % 5 :=
    finset_inert_product_sq_mod_five
      (fun p hp => (hskeleton p hp).1)
  have hfour (k : ℕ) : 4 ^ (2 * k) % 5 = 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add,
          Nat.mul_mod, ih]
        norm_num
  have hnSq : n ^ 2 % 5 = 1 := by
    rw [← hprod, hsquareProduct, hk]
    simpa [two_mul] using hfour k
  exact hbad hnSq

/-- A composite squarefree candidate in the odd-cardinality quartic
skeleton has at least three distinct prime factors.-/
theorem quarticSkeleton_card_ge_three {n : ℕ}
    (hn : SquarefreeCounterexampleCandidate n) (hskeleton : QuarticSkeleton n) :
    3 ≤ n.primeFactors.card := by
  rcases hn with ⟨hsq, hnprime, _h5, _hglobal, _hbad⟩
  have hodd : Odd n.primeFactors.card :=
    quarticSkeleton_card_odd
      ⟨hsq, hnprime, _h5, _hglobal, _hbad⟩ hskeleton
  by_contra hnot
  have hlt : n.primeFactors.card < 3 := Nat.lt_of_not_ge hnot
  rcases hodd with ⟨k, hk⟩
  have hcard : n.primeFactors.card = 1 := by omega
  obtain ⟨p, hpf⟩ := Finset.card_eq_one.mp hcard
  have hpMem : p ∈ n.primeFactors := by simp [hpf]
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hprod : (∏ q ∈ n.primeFactors, q) = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hpn : p = n := by simpa [hpf] using hprod
  exact hnprime (hpn ▸ hpPrime)

/-- **H4-to-skeleton reduction, kernel-pure.**

For a squarefree candidate, local H4 forces every prime factor into an
inert residue class.  The global polynomial congruence simultaneously
supplies the exact complementary local row at every factor.-/
theorem quarticSkeleton_of_candidate_localH4 {n : ℕ}
    (hn : SquarefreeCounterexampleCandidate n) (hlocal : LocalH4For n) :
    QuarticSkeleton n := by
  rcases hn with ⟨_hsq, _hnprime, h5, hglobal, hbad⟩
  have hnInert : InertModFive n :=
    inertModFive_of_square_ne_one h5 hbad
  intro p hpmem
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hp5 : p ≠ 5 := by
    intro hp
    exact h5 (hp ▸ hpdvd)
  have hrow : LocalS5 p (n / p) :=
    localS5_of_global_factor hp5 hpdvd hglobal
  have hnotSplit : ¬ SplitModFive p := by
    intro hpSplit
    have hp2 : p ≠ 2 := by
      intro hp
      subst p
      simp [SplitModFive] at hpSplit
    have hquotient : InertModFive (n / p) :=
      inertModFive_div_of_splitModFive hpdvd hpSplit hnInert
    have htransport : HasOrderFourTransport p :=
      hasOrderFourTransport_of_local hp2 hp5 hrow hquotient
    exact hlocal p hpp hpdvd
      (isSquare_five_of_split hp2 hpSplit) htransport
  have hp0 : p % 5 ≠ 0 := by
    intro hp0
    have hfive : 5 ∣ p := Nat.dvd_of_mod_eq_zero hp0
    exact hp5
      ((Nat.prime_dvd_prime_iff_eq (by norm_num) hpp).mp hfive).symm
  have hplt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
  have hpInert : InertModFive p := by
    interval_cases hpmod : p % 5 <;>
      simp [SplitModFive, InertModFive, hpmod] at hp0 hnotSplit ⊢
  exact ⟨hpInert, hrow⟩

/-- **Concrete witness dichotomy.**

No arithmetic reduction is assumed here: every squarefree counterexample
candidate either already exhibits a split order-four witness, or its full
family of complementary local rows forms the inert quartic skeleton.-/
theorem squarefree_counterexample_concrete_dichotomy
    {n : ℕ} (hn : SquarefreeCounterexampleCandidate n) :
    SplitOrderFourWitness n ∨
      (QuarticSkeleton n ∧ Odd n.primeFactors.card
        ∧ 3 ≤ n.primeFactors.card) := by
  by_cases hlocal : LocalH4For n
  · have hskeleton := quarticSkeleton_of_candidate_localH4 hn hlocal
    exact Or.inr
      ⟨hskeleton, quarticSkeleton_card_odd hn hskeleton,
        quarticSkeleton_card_ge_three hn hskeleton⟩
  · exact Or.inl
      ((not_localH4For_iff_splitOrderFourWitness n).mp hlocal)

/-- The generic interface starts *after* the concrete quartic skeleton: it
asks subsequent arithmetic theory to turn that skeleton into its chosen
finite-fiber witness. `ExplicitFiber.lean` supplies a concrete instance.-/
def SkeletonToFiber (FiberWitness : ℕ → Prop) : Prop :=
  ∀ n, SquarefreeCounterexampleCandidate n → QuarticSkeleton n →
    FiberWitness n

/-- **DICOTOMIA LOGICA, forma kernel-pura.** Dalla premessa esplicita che
la riduzione aritmetica sia valida *dopo lo scheletro quartico concreto*
segue che ogni candidato globale esibisce o un fattore split con trasporto
di ordine quattro, oppure un testimone nella fibra globale.-/
theorem squarefree_counterexample_witness_dichotomy
    {FiberWitness : ℕ → Prop}
    (hreduce : SkeletonToFiber FiberWitness)
    {n : ℕ} (hn : SquarefreeCounterexampleCandidate n) :
    SplitOrderFourWitness n ∨ FiberWitness n := by
  rcases squarefree_counterexample_concrete_dichotomy hn with
    hsplit | ⟨hskeleton, _hodd, _hcard⟩
  · exact Or.inl hsplit
  · exact Or.inr (hreduce n hn hskeleton)

/-- Se entrambi i tipi di certificato vengono esclusi, non resta alcun
candidato globale. È la forma di chiusura richiesta al futuro montaggio.-/
theorem no_squarefree_counterexample_of_no_witnesses
    {FiberWitness : ℕ → Prop}
    (hreduce : SkeletonToFiber FiberWitness)
    (hlocal : ∀ n, ¬ SplitOrderFourWitness n)
    (hfiber : ∀ n, ¬ FiberWitness n) :
    ∀ n, ¬ SquarefreeCounterexampleCandidate n := by
  intro n hn
  rcases squarefree_counterexample_witness_dichotomy hreduce hn with
    hsplit | hglobal
  · exact hlocal n hsplit
  · exact hfiber n hglobal

end AgrawalCore
