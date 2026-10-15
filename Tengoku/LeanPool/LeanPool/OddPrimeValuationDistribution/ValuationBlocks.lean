/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.OddPrimeValuationDistribution.CarryPolynomial
public import Tengoku

/-!
# Exact central-binomial valuation distributions for odd primes

For the odd prime `p = 2 * half + 1`, this module identifies fixed-length
base-`p` words with the integers below `p ^ length`.  Kummer's theorem turns
the word carry count into the exact value of `ν_p (centralBinom n)`, so the
transfer recurrence becomes an arithmetic distribution theorem.
-/

@[expose] public section

namespace OddPrimeValuationDistribution

open Nat Polynomial
open scoped BigOperators

/-- Natural value of a fixed-length word in the odd base `2 * half + 1`. -/
def oddCarryWordValue {half length : ℕ}
    (word : List.Vector (Fin (oddBase half)) length) : ℕ :=
  Nat.ofDigits (oddBase half) (oddCarryWordDigits word)

/--
@isnad1 id=lt.1h3v.s5.6c6e9771e121 from=translated src=- shape=65890cbe vocab=6e876598
-/
lemma oddCarryWordValue_lt {half length : ℕ} (hhalf : 0 < half)
    (word : List.Vector (Fin (oddBase half)) length) :
    oddCarryWordValue word < oddBase half ^ length := by
  simpa [oddCarryWordValue, oddCarryWordDigits] using
    (Nat.ofDigits_lt_base_pow_length (b := oddBase half)
      (oddBase_one_lt hhalf)
      (by simp [oddCarryWordDigits] :
        ∀ digit ∈ oddCarryWordDigits word, digit < oddBase half))

/-- The word value packaged in the corresponding complete finite block. -/
def oddCarryWordValueFin {half length : ℕ} (hhalf : 0 < half)
    (word : List.Vector (Fin (oddBase half)) length) :
    Fin (oddBase half ^ length) :=
  ⟨oddCarryWordValue word, oddCarryWordValue_lt hhalf word⟩

/--
@isnad1 id=injectiv.1h2v.s5.2afd9840173c from=translated src=- shape=99c7698e vocab=b898682e
-/
lemma oddCarryWordValueFin_injective
    (half : ℕ) (hhalf : 0 < half) (length : ℕ) :
    Function.Injective
      (oddCarryWordValueFin hhalf :
        List.Vector (Fin (oddBase half)) length →
          Fin (oddBase half ^ length)) := by
  intro word₁ word₂ hvalue
  apply List.Vector.toList_injective
  apply (List.map_injective_iff.mpr Fin.val_injective)
  apply Nat.ofDigits_inj_of_len_eq
    (b := oddBase half) (oddBase_one_lt hhalf)
  · simp
  · simp
  · simp
  · exact congrArg Fin.val hvalue

/-- Positional notation is a bijection from fixed-length odd-base words to
the corresponding complete block of natural numbers. -/
noncomputable def oddCarryWordValueEquiv
    (half : ℕ) (hhalf : 0 < half) (length : ℕ) :
    List.Vector (Fin (oddBase half)) length ≃
      Fin (oddBase half ^ length) :=
  Equiv.ofBijective (oddCarryWordValueFin hhalf) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨oddCarryWordValueFin_injective half hhalf length, by simp⟩

/--
@isnad1 id=eq.1h3v.s5.41354038b605 from=translated src=- shape=a2c86112 vocab=06caa03c
-/
lemma padicValNat_oddPrime_centralBinom_word_eq_carryCount
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    {length : ℕ} (word : List.Vector (Fin (oddBase half)) length) :
    padicValNat (oddBase half)
        (Nat.centralBinom (oddCarryWordValue word)) =
      oddDoubleCarryCountAux half (oddCarryWordDigits word) 0 := by
  exact padicValNat_oddPrime_centralBinom_ofDigits_eq_carryCount
    half hhalf _ (by simp [oddCarryWordDigits])

/-- Polynomial distribution of exact odd-prime valuations on the complete
block `0 ≤ n < p ^ length`. -/
noncomputable def oddPrimeValuationPolynomial
    (half length : ℕ) : Polynomial ℕ :=
  ∑ n : Fin (oddBase half ^ length),
    X ^ padicValNat (oddBase half) (Nat.centralBinom n.val)

/-- The odd-prime valuation distribution is exactly the doubling-carry
distribution.
@isnad1 id=eq.1h2v.s4.7b42d18358e7 from=translated src=- shape=22f9a9a5 vocab=d566ea6f
-/
theorem oddPrimeValuationPolynomial_eq_carryPolynomial
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length : ℕ) :
    oddPrimeValuationPolynomial half length =
      oddCarryPolynomial half length := by
  unfold oddPrimeValuationPolynomial oddCarryPolynomial
  symm
  exact Fintype.sum_equiv (oddCarryWordValueEquiv half hhalf length) _ _
    (fun word => by
      change
        X ^ oddDoubleCarryCountAux half (oddCarryWordDigits word) 0 =
          X ^ padicValNat (oddBase half)
            (Nat.centralBinom (oddCarryWordValue word))
      rw [padicValNat_oddPrime_centralBinom_word_eq_carryCount half hhalf])

/-- Integers in a complete odd-prime block with a prescribed exact
central-binomial valuation. -/
abbrev OddPrimeBlockWithValuation (half length value : ℕ) :=
  {n : Fin (oddBase half ^ length) //
    padicValNat (oddBase half) (Nat.centralBinom n.val) = value}

/-- Literal coefficient interpretation of the odd-prime valuation
polynomial.
@isnad1 id=eq.0h3v.s7.622e9e3b451b from=translated src=- shape=b40e679b vocab=e23202c2
-/
theorem coeff_oddPrimeValuationPolynomial
    (half length value : ℕ) :
    (oddPrimeValuationPolynomial half length).coeff value =
      Fintype.card (OddPrimeBlockWithValuation half length value) := by
  classical
  simp only [oddPrimeValuationPolynomial, finsetSum_coeff, coeff_X_pow,
    Finset.sum_boole, cast_id, OddPrimeBlockWithValuation]
  rw [Fintype.card_subtype]
  congr 1
  ext n
  simp [eq_comm]

/-- Headline exact-distribution recurrence for every odd prime
`p = 2 * half + 1`.
@isnad1 id=eq.1h2v.s7.9b545571e840 from=translated src=- shape=54f65955 vocab=2344d315
-/
theorem oddPrimeValuationPolynomial_recurrence
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length : ℕ) :
    oddPrimeValuationPolynomial half (length + 2) +
        (oddBase half : Polynomial ℕ) * X *
          oddPrimeValuationPolynomial half length =
      ((half + 1 : ℕ) : Polynomial ℕ) * (1 + X) *
        oddPrimeValuationPolynomial half (length + 1) := by
  simp only [oddPrimeValuationPolynomial_eq_carryPolynomial half hhalf]
  exact oddCarryPolynomial_recurrence half length

end OddPrimeValuationDistribution
