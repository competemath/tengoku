module
public import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section
namespace Tengoku.Stafford38Formal end Tengoku.Stafford38Formal open Tengoku.Stafford38Formal 
open IsLocalRing

universe u

def _root_.Tengoku.Stafford38Formal.castAtPrimeLocalization
    {R : Type u} [CommRing R] {P Q : Ideal R} [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q) (x : Localization.AtPrime Q) : Localization.AtPrime P := by
  cases hPQ
  exact x

/-- Transport a unit factorization in the localization at one prime along an
equality of primes.  This preserves the same base elements and exponent; only
the localization carrier of the unit changes.
@isnad1 id=and.3h7v.s10.7f52ff977131 from=translated src=- shape=7ee6f4ef vocab=da7ae508
-/
theorem _root_.Tengoku.Stafford38Formal.unit_power_factor_transport
    {R : Type u} [CommRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q)
    (q s : R) (n : ℕ) (uQ : Localization.AtPrime Q)
    (huQ : IsUnit uQ)
    (hfactor : algebraMap R (Localization.AtPrime Q) q =
      (algebraMap R (Localization.AtPrime Q) s) ^ n * uQ) :
    IsUnit (castAtPrimeLocalization hPQ uQ) ∧
      algebraMap R (Localization.AtPrime P) q =
        (algebraMap R (Localization.AtPrime P) s) ^ n *
          castAtPrimeLocalization hPQ uQ := by
  cases hPQ
  exact ⟨huQ, hfactor⟩

/-- The two retained powers can be moved together without changing either
exponent or the shared uniformizer.
@isnad1 id=ex.5h10v.s11.52634abbf749 from=translated src=- shape=e6af3677 vocab=8f0cdc68
-/
theorem _root_.Tengoku.Stafford38Formal.two_unit_power_factors_transport
    {R : Type u} [CommRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q)
    (q₀ q₁ s : R) (n₀ n₁ : ℕ)
    (u₀Q u₁Q : Localization.AtPrime Q)
    (hu₀Q : IsUnit u₀Q) (hu₁Q : IsUnit u₁Q)
    (hfactor₀ : algebraMap R (Localization.AtPrime Q) q₀ =
      (algebraMap R (Localization.AtPrime Q) s) ^ n₀ * u₀Q)
    (hfactor₁ : algebraMap R (Localization.AtPrime Q) q₁ =
      (algebraMap R (Localization.AtPrime Q) s) ^ n₁ * u₁Q) :
    ∃ u₀P u₁P : Localization.AtPrime P,
      IsUnit u₀P ∧ IsUnit u₁P ∧
      algebraMap R (Localization.AtPrime P) q₀ =
        (algebraMap R (Localization.AtPrime P) s) ^ n₀ * u₀P ∧
      algebraMap R (Localization.AtPrime P) q₁ =
        (algebraMap R (Localization.AtPrime P) s) ^ n₁ * u₁P := by
  refine ⟨castAtPrimeLocalization hPQ u₀Q,
    castAtPrimeLocalization hPQ u₁Q, ?_, ?_, ?_, ?_⟩
  · exact (unit_power_factor_transport P Q hPQ q₀ s n₀ u₀Q hu₀Q hfactor₀).1
  · exact (unit_power_factor_transport P Q hPQ q₁ s n₁ u₁Q hu₁Q hfactor₁).1
  · exact (unit_power_factor_transport P Q hPQ q₀ s n₀ u₀Q hu₀Q hfactor₀).2
  · exact (unit_power_factor_transport P Q hPQ q₁ s n₁ u₁Q hu₁Q hfactor₁).2

/-- The exact shape needed by the same-witness caller: the retained column
factors are first obtained at `centerB`, while the public certificate is
indexed by `PB`.  This changes only the localization of each unit; the same
`s`, `q₀`, `q₁`, and strict-order exponents `a < a + e` remain.
@isnad1 id=ex.5h10v.s11.90ffa17e7070 from=translated src=- shape=1d292f4f vocab=60d0b869
-/
theorem _root_.Tengoku.Stafford38Formal.selected_center_retained_factors_at_canonical_prime
    {B : Type u} [CommRing B]
    (PB centerB : Ideal B) [PB.IsPrime] [centerB.IsPrime]
    (hPB_eq : PB = centerB)
    (q₀ q₁ s : B) (a e : ℕ)
    (u₀ u₁ : Localization.AtPrime centerB)
    (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
    (hfactor₀ : algebraMap B (Localization.AtPrime centerB) q₀ =
      (algebraMap B (Localization.AtPrime centerB) s) ^ a * u₀)
    (hfactor₁ : algebraMap B (Localization.AtPrime centerB) q₁ =
      (algebraMap B (Localization.AtPrime centerB) s) ^ (a + e) * u₁) :
    ∃ u₀PB u₁PB : Localization.AtPrime PB,
      IsUnit u₀PB ∧ IsUnit u₁PB ∧
      algebraMap B (Localization.AtPrime PB) q₀ =
        (algebraMap B (Localization.AtPrime PB) s) ^ a * u₀PB ∧
      algebraMap B (Localization.AtPrime PB) q₁ =
        (algebraMap B (Localization.AtPrime PB) s) ^ (a + e) * u₁PB := by
  exact two_unit_power_factors_transport PB centerB hPB_eq q₀ q₁ s a (a + e)
    u₀ u₁ hu₀ hu₁ hfactor₀ hfactor₁

/-- The same explicit equality elimination transports the local maximal-ideal
generator statement; rewriting under `AtPrime` can fail because its ring
instance is indexed by the prime.
@isnad1 id=eq.2h4v.s9.735068d38eda from=translated src=- shape=045ba5fa vocab=092cb848
-/
theorem _root_.Tengoku.Stafford38Formal.prime_span_eq_maximalIdeal_transport
    {R : Type u} [CommRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q) (s : R)
    (hspan : Ideal.span {algebraMap R (Localization.AtPrime Q) s} =
      maximalIdeal (Localization.AtPrime Q)) :
    Ideal.span {algebraMap R (Localization.AtPrime P) s} =
      maximalIdeal (Localization.AtPrime P) := by
  cases hPQ
  exact hspan
-- Tengoku: root names of this library moved to Tengoku.Stafford38Formal so they do not collide with other libraries (generated)
