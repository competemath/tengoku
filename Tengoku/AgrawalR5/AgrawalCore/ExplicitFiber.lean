/-
Agrawal r = 5 — FROM THE QUARTIC SKELETON TO EXPLICIT RESULTANT FIBERS.

This module closes the last abstract interface between the concrete
quartic skeleton and the two finite-resultant branches.  For every prime
factor `q` of a squarefree candidate in the skeleton, put

  A = n / q - 1.

The complementary local row is then literally the row at exponent `A + 1`.
Its residue modulo `5` selects exactly one of the two resultants

  Res(Φ₅, (X - 1)^A - 1),
  Res(Φ₅, X (X - 1)^A + 1).

The kernel proves both the fourth-power divisibility and the closed
archimedean bound `q^4 ≤ 16 * 5^A`.  This is a reduction theorem only:
it does not assert that any of the resulting fibers is empty.
-/
import Tengoku.AgrawalR5.AgrawalCore.ResultantTrap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- Every complementary quotient in a squarefree quartic skeleton with at
least three prime factors is nontrivial.
@isnad1 id=lt.3h2v.s5.d7c4a6f787ae from=translated src=- shape=917d6441 vocab=6e937422
-/
theorem quotient_gt_one_of_quarticSkeleton
    {n q : ℕ} (hn : SquarefreeCounterexampleCandidate n)
    (hskeleton : QuarticSkeleton n) (hq : q ∈ n.primeFactors) :
    1 < n / q := by
  have hcard : 3 ≤ n.primeFactors.card :=
    quarticSkeleton_card_ge_three hn hskeleton
  have herase : (n.primeFactors.erase q).Nonempty := by
    have hcardErase :
        (n.primeFactors.erase q).card = n.primeFactors.card - 1 :=
      Finset.card_erase_of_mem hq
    have : 0 < (n.primeFactors.erase q).card := by omega
    exact Finset.card_pos.mp this
  have hprime :
      ∀ p ∈ n.primeFactors.erase q, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hprod :
      (∏ p ∈ n.primeFactors.erase q, p) = n / q := by
    have hsq : Squarefree n := hn.1
    have hsubset : ({q} : Finset ℕ) ⊆ n.primeFactors := by
      simpa using hq
    have h :=
      Nat.prod_primeFactors_sdiff_of_squarefree hsq hsubset
    simpa [Finset.sdiff_singleton_eq_erase] using h
  rw [← hprod]
  obtain ⟨p, hp⟩ := herase
  have hprodPos :
      0 < ∏ a ∈ n.primeFactors.erase q, a :=
    Finset.prod_pos fun a ha => (hprime a ha).pos
  have hpDvd :
      p ∣ ∏ a ∈ n.primeFactors.erase q, a := by
    exact Finset.dvd_prod_of_mem (fun a => a) hp
  exact (hprime p hp).one_lt.trans_le (Nat.le_of_dvd hprodPos hpDvd)

/-- The complete arithmetic certificate carried by one terminal resultant.-/
def ResultantFiberBounds (q A : ℕ) (R : ℤ) : Prop :=
  (q : ℤ) ^ 4 ∣ R
    ∧ R ≠ 0
    ∧ q ^ 4 ≤ Int.natAbs R
    ∧ Int.natAbs R ≤ 16 * 5 ^ A

/-- The full family of explicit resultant rows attached to a candidate.

The definition records the branch residue, fourth-power divisibility of the
corresponding integral resultant, its nonvanishing, and the exact two-sided
size trap.-/
def ExplicitResultantRows (n : ℕ) : Prop :=
  ∀ q (_hq : q ∈ n.primeFactors),
    let A := n / q - 1
    (((n / q) % 5 = 1
        ∧ ResultantFiberBounds q A
          ((cyclotomic 5 ℤ).resultant (pureFiberPolynomial A)))
      ∨ ((n / q) % 5 = 4
        ∧ ResultantFiberBounds q A
          ((cyclotomic 5 ℤ).resultant (twistedFiberPolynomial A))))

/-- **Skeleton-to-explicit-fibers, kernel-pure.**

Every factor of the quartic skeleton lands in exactly one of the pure and
twisted finite-resultant branches, with both divisibility and size bound
proved in the kernel.
@isnad1 id=skeleton.0h0v.s1.62b3f5dbc0b9 from=translated src=- shape=49959d42 vocab=7c9a55ad
-/
theorem explicitResultantRows_of_skeleton :
    SkeletonToFiber ExplicitResultantRows := by
  intro n hn hskeleton q hq
  letI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  have hquot : 1 < n / q :=
    quotient_gt_one_of_quarticSkeleton hn hskeleton hq
  let A := n / q - 1
  have hA : 0 < A := by
    dsimp [A]
    omega
  have hAone : A + 1 = n / q := by
    dsimp [A]
    omega
  have hrow : LocalS5 q (A + 1) := by
    rw [hAone]
    exact (hskeleton q hq).2
  have hsplit : SplitModFive (n / q) := by
    have hpdvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq
    have hnInert : InertModFive n :=
      inertModFive_of_square_ne_one hn.2.2.1 hn.2.2.2.2
    exact splitModFive_div_of_inertModFive hpdvd
      (hskeleton q hq).1 hnInert
  rcases hsplit with hpure | htwisted
  · left
    have hres : (A + 1) % 5 = 1 := by
      rw [hAone]
      exact hpure
    refine ⟨hpure, ?_, ?_, ?_, ?_⟩
    · exact pure_row_pow_four_dvd_resultant (hskeleton q hq).1 hres hrow
    · exact pure_resultant_ne_zero hA
    · exact pure_row_pow_four_le_resultant_natAbs
        (hskeleton q hq).1 hA hres hrow
    · exact pure_resultant_natAbs_le A
  · right
    have hres : (A + 1) % 5 = 4 := by
      rw [hAone]
      exact htwisted
    refine ⟨htwisted, ?_, ?_, ?_, ?_⟩
    · exact twisted_row_pow_four_dvd_resultant (hskeleton q hq).1 hres hrow
    · exact twisted_resultant_ne_zero A
    · exact twisted_row_pow_four_le_resultant_natAbs
        (hskeleton q hq).1 hres hrow
    · exact twisted_resultant_natAbs_le A

/-- The global witness dichotomy with the formerly abstract fiber witness
instantiated by the literal pure/twisted resultant rows.
@isnad1 id=or.1h1v.s3.276f2ce32dd8 from=translated src=- shape=2b510e99 vocab=697f39f8
-/
theorem squarefree_counterexample_explicit_resultant_dichotomy
    {n : ℕ} (hn : SquarefreeCounterexampleCandidate n) :
    SplitOrderFourWitness n ∨ ExplicitResultantRows n :=
  squarefree_counterexample_witness_dichotomy
    explicitResultantRows_of_skeleton hn

/-- **Exact two-wall closure statement.**

If split order-four witnesses are universally excluded and no number carries
the explicit family of terminal resultant rows, then there is no squarefree
counterexample candidate.  The two premises are intentionally visible: this
theorem packages the completed reduction and proves neither open wall.
@isnad1 id=not.2h1v.s4.07187500361f from=translated src=- shape=5598dfbd vocab=697f39f8
-/
theorem no_squarefree_counterexample_of_no_split_and_no_explicit_rows
    (hsplit : ∀ n, SquarefreeCounterexampleCandidate n →
      ¬ SplitOrderFourWitness n)
    (hfiber : ∀ n, SquarefreeCounterexampleCandidate n →
      ¬ ExplicitResultantRows n) :
    ∀ n, ¬ SquarefreeCounterexampleCandidate n := by
  intro n hn
  rcases squarefree_counterexample_explicit_resultant_dichotomy hn with
    hlocal | hresultant
  · exact hsplit n hn hlocal
  · exact hfiber n hn hresultant

end AgrawalCore
