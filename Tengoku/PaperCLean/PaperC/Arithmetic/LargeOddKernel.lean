import Tengoku.PaperCLean.PaperC.Arithmetic.DefectivePredicate
import Tengoku.Seed.Data.Nat.Squarefree
import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The large odd kernel

For a cutoff `B` and an integer `n`, the large odd kernel is the product of
the primes `p > B` which occur to odd order in `n`.  This is the canonical
integer denoted `𝒦_B(n)` in Lemma 4.2 of Paper C.

Besides the defining support characterization, this file records the
properties used by the counting argument: the kernel is a nonzero squarefree
divisor of `n`, its prime factors recover its defining support, and the
canonical odd-support decomposition of `n` splits into coprime small and
large parts.
-/

namespace PaperC
namespace LargeOddKernel

open scoped BigOperators

open DefectivePredicate

/-- The odd-valuation primes of `n` lying strictly above `B`.-/
noncomputable def largeOddPrimeSupport (B n : ℕ) : Finset ℕ :=
  (oddPrimeSupport n).filter fun p ↦ B < p

/-- The odd-valuation primes of `n` lying at or below `B`.-/
noncomputable def smallOddPrimeSupport (B n : ℕ) : Finset ℕ :=
  (oddPrimeSupport n).filter fun p ↦ p ≤ B

/-- The product of the odd-valuation primes of `n` lying strictly above `B`.-/
noncomputable def largeOddKernel (B n : ℕ) : ℕ :=
  (largeOddPrimeSupport B n).prod id

/-- The complementary squarefree part supported on primes at most `B`.-/
noncomputable def smallOddPart (B n : ℕ) : ℕ :=
  (smallOddPrimeSupport B n).prod id

/--
@isnad1 id=iff.0h3v.s5.3ecf29a7985d from=translated src=- shape=1f1b7d97 vocab=25b2dcaa
-/
@[simp]
theorem mem_largeOddPrimeSupport {B n p : ℕ} :
    p ∈ largeOddPrimeSupport B n ↔
      p ∈ oddPrimeSupport n ∧ B < p := by
  simp [largeOddPrimeSupport]

/--
@isnad1 id=iff.0h3v.s5.eb3f6465f469 from=translated src=- shape=afce2b0f vocab=c60d9df5
-/
@[simp]
theorem mem_smallOddPrimeSupport {B n p : ℕ} :
    p ∈ smallOddPrimeSupport B n ↔
      p ∈ oddPrimeSupport n ∧ p ≤ B := by
  simp [smallOddPrimeSupport]

/-- The canonical odd support is exactly the support of the parity vector.
@isnad1 id=iff.0h2v.s6.15dac360daae from=translated src=- shape=a2334ea9 vocab=7e43d6e2
-/
theorem mem_oddPrimeSupport_iff_parityVec_ne_zero {n p : ℕ} :
    p ∈ oddPrimeSupport n ↔ parityVec n p ≠ 0 := by
  simp only [oddPrimeSupport, oddFactorization, parityVec,
    Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq,
    ZMod.natCast_eq_zero_iff]
  constructor
  · intro h hp
    exact h (Nat.mod_eq_zero_of_dvd hp)
  · intro h hp
    exact h (Nat.dvd_of_mod_eq_zero hp)

/-- Membership in the large support, expressed directly through `parityVec`.
@isnad1 id=iff.0h3v.s6.3481c424cdfe from=translated src=- shape=677a484f vocab=00982798
-/
theorem mem_largeOddPrimeSupport_iff {B n p : ℕ} :
    p ∈ largeOddPrimeSupport B n ↔
      B < p ∧ parityVec n p ≠ 0 := by
  rw [mem_largeOddPrimeSupport, mem_oddPrimeSupport_iff_parityVec_ne_zero]
  exact and_comm

/-- Membership in the small support, expressed directly through `parityVec`.
@isnad1 id=iff.0h3v.s6.8b6c2b596952 from=translated src=- shape=ce74356c vocab=d81eef37
-/
theorem mem_smallOddPrimeSupport_iff {B n p : ℕ} :
    p ∈ smallOddPrimeSupport B n ↔
      p ≤ B ∧ parityVec n p ≠ 0 := by
  rw [mem_smallOddPrimeSupport, mem_oddPrimeSupport_iff_parityVec_ne_zero]
  exact and_comm

/-- Every coordinate in the odd support is a genuine prime.
@isnad1 id=prime.1h2v.s4.0803222c1533 from=translated src=- shape=0816e5b4 vocab=d30bbf2b
-/
theorem prime_of_mem_oddPrimeSupport {n p : ℕ}
    (hp : p ∈ oddPrimeSupport n) :
    p.Prime := by
  apply Nat.prime_of_mem_primeFactors
  exact Finsupp.support_mapRange hp

/-- Every prime in the large support lies above the cutoff.
@isnad1 id=and.1h3v.s4.aa6f834799f0 from=translated src=- shape=e56fe9ca vocab=350ff442
-/
theorem prime_and_large_of_mem_largeOddPrimeSupport {B n p : ℕ}
    (hp : p ∈ largeOddPrimeSupport B n) :
    p.Prime ∧ B < p := by
  exact ⟨prime_of_mem_oddPrimeSupport (mem_largeOddPrimeSupport.mp hp).1,
    (mem_largeOddPrimeSupport.mp hp).2⟩

/-- Every prime in the small support lies below the inclusive cutoff.
@isnad1 id=and.1h3v.s4.3e8fdba24e54 from=translated src=- shape=1647df11 vocab=68443691
-/
theorem prime_and_small_of_mem_smallOddPrimeSupport {B n p : ℕ}
    (hp : p ∈ smallOddPrimeSupport B n) :
    p.Prime ∧ p ≤ B := by
  exact ⟨prime_of_mem_oddPrimeSupport (mem_smallOddPrimeSupport.mp hp).1,
    (mem_smallOddPrimeSupport.mp hp).2⟩

/--
For a prime above the cutoff, a nonzero parity coordinate is equivalent to
membership in the large odd support.
@isnad1 id=iff.2h3v.s6.ba020cf71183 from=translated src=- shape=842fc175 vocab=0caaac88
-/
theorem parityVec_ne_zero_iff_mem_largeOddPrimeSupport
    {B n p : ℕ} (_hp : p.Prime) (hpB : B < p) :
    parityVec n p ≠ 0 ↔ p ∈ largeOddPrimeSupport B n := by
  rw [mem_largeOddPrimeSupport_iff]
  simp [hpB]

/-! ## Arithmetic properties of the support and its product -/

/-- Complete valuation characterization of the large support.
@isnad1 id=iff.0h3v.s5.548be992a4bb from=translated src=- shape=0130ca79 vocab=204ee51b
-/
theorem mem_largeOddPrimeSupport_iff_prime_large_odd {B n p : ℕ} :
    p ∈ largeOddPrimeSupport B n ↔
      p.Prime ∧ B < p ∧ Odd (n.factorization p) := by
  constructor
  · intro hp
    exact ⟨(prime_and_large_of_mem_largeOddPrimeSupport hp).1,
      (prime_and_large_of_mem_largeOddPrimeSupport hp).2,
      ZMod.natCast_ne_zero_iff_odd.mp (by
        simpa only [parityVec_apply] using
          (mem_largeOddPrimeSupport_iff.mp hp).2)⟩
  · rintro ⟨_hpPrime, hpB, hpOdd⟩
    rw [mem_largeOddPrimeSupport_iff, parityVec_apply]
    exact ⟨hpB, ZMod.natCast_ne_zero_iff_odd.mpr hpOdd⟩

/-- Complete valuation characterization of the small support.
@isnad1 id=iff.0h3v.s5.9959dfd3049f from=translated src=- shape=6d062861 vocab=2562f9c1
-/
theorem mem_smallOddPrimeSupport_iff_prime_small_odd {B n p : ℕ} :
    p ∈ smallOddPrimeSupport B n ↔
      p.Prime ∧ p ≤ B ∧ Odd (n.factorization p) := by
  constructor
  · intro hp
    exact ⟨(prime_and_small_of_mem_smallOddPrimeSupport hp).1,
      (prime_and_small_of_mem_smallOddPrimeSupport hp).2,
      ZMod.natCast_ne_zero_iff_odd.mp (by
        simpa only [parityVec_apply] using
          (mem_smallOddPrimeSupport_iff.mp hp).2)⟩
  · rintro ⟨_hpPrime, hpB, hpOdd⟩
    rw [mem_smallOddPrimeSupport_iff, parityVec_apply]
    exact ⟨hpB, ZMod.natCast_ne_zero_iff_odd.mpr hpOdd⟩

/-- The large support is a finite subset of the prime factors of `n`.
@isnad1 id=le.0h2v.s4.912fdf56fe25 from=translated src=- shape=87ff9306 vocab=04e0ee56
-/
theorem largeOddPrimeSupport_subset_primeFactors (B n : ℕ) :
    largeOddPrimeSupport B n ⊆ n.primeFactors := by
  intro p hp
  exact Finsupp.support_mapRange (mem_largeOddPrimeSupport.mp hp).1

/-- The small support is a finite subset of the prime factors of `n`.
@isnad1 id=le.0h2v.s4.b68cab888b3d from=translated src=- shape=87ff9306 vocab=7c34d256
-/
theorem smallOddPrimeSupport_subset_primeFactors (B n : ℕ) :
    smallOddPrimeSupport B n ⊆ n.primeFactors := by
  intro p hp
  exact Finsupp.support_mapRange (mem_smallOddPrimeSupport.mp hp).1

/-- The large odd kernel never vanishes, including for `n = 0`.
@isnad1 id=ne.0h2v.s3.25a6f0977405 from=translated src=- shape=aa052b1b vocab=db97f72d
-/
theorem largeOddKernel_ne_zero (B n : ℕ) :
    largeOddKernel B n ≠ 0 := by
  rw [largeOddKernel, Finset.prod_ne_zero_iff]
  intro p hp
  exact (prime_and_large_of_mem_largeOddPrimeSupport hp).1.ne_zero

/-- The complementary small odd part never vanishes.
@isnad1 id=ne.0h2v.s3.d0334bfbd3b7 from=translated src=- shape=aa052b1b vocab=8aeb1894
-/
theorem smallOddPart_ne_zero (B n : ℕ) :
    smallOddPart B n ≠ 0 := by
  rw [smallOddPart, Finset.prod_ne_zero_iff]
  intro p hp
  exact (prime_and_small_of_mem_smallOddPrimeSupport hp).1.ne_zero

/--
The product of a finite set of primes remembers the set.  This is the
injectivity statement used implicitly whenever an odd kernel is identified
through its prime support.
@isnad1 id=eq.3h2v.s6.454fe992e92d from=translated src=- shape=9cfaae75 vocab=486d70d3
-/
theorem primeFinset_product_injective
    {s t : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime)
    (ht : ∀ p ∈ t, p.Prime)
    (hprod : s.prod id = t.prod id) :
    s = t := by
  calc
    s = (s.prod id).primeFactors := (Nat.primeFactors_prod hs).symm
    _ = (t.prod id).primeFactors := congrArg Nat.primeFactors hprod
    _ = t := Nat.primeFactors_prod ht

/-- The defining support is recovered exactly from the kernel.
@isnad1 id=eq.0h2v.s3.a8f9ef2ecc00 from=translated src=- shape=43d4370a vocab=6480670a
-/
theorem primeFactors_largeOddKernel (B n : ℕ) :
    (largeOddKernel B n).primeFactors = largeOddPrimeSupport B n := by
  rw [largeOddKernel]
  exact Nat.primeFactors_prod fun p hp ↦
    (prime_and_large_of_mem_largeOddPrimeSupport hp).1

/-- The small odd support is recovered exactly from its product.
@isnad1 id=eq.0h2v.s3.15cf7c5c9cd5 from=translated src=- shape=43d4370a vocab=40004ba1
-/
theorem primeFactors_smallOddPart (B n : ℕ) :
    (smallOddPart B n).primeFactors = smallOddPrimeSupport B n := by
  rw [smallOddPart]
  exact Nat.primeFactors_prod fun p hp ↦
    (prime_and_small_of_mem_smallOddPrimeSupport hp).1

/-- A finite product of distinct natural primes is squarefree.-/
private theorem squarefree_prod_primes
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert p s hp ih =>
      have hpPrime : p.Prime := hs p (Finset.mem_insert_self p s)
      have hsPrime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp]
      apply (Nat.squarefree_mul ?_).mpr
      · exact ⟨hpPrime.squarefree, ih hsPrime⟩
      · apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpPrime (hsPrime q hq)).mpr
        intro hpq
        apply hp
        rwa [hpq]

/-- The large odd kernel is squarefree.
@isnad1 id=squarefr.0h2v.s3.060adcc42990 from=translated src=- shape=80310a19 vocab=8747a78f
-/
theorem largeOddKernel_squarefree (B n : ℕ) :
    Squarefree (largeOddKernel B n) := by
  rw [largeOddKernel]
  exact squarefree_prod_primes _ fun p hp ↦
    (prime_and_large_of_mem_largeOddPrimeSupport hp).1

/-- The complementary small odd part is squarefree.
@isnad1 id=squarefr.0h2v.s3.567656cb8cc9 from=translated src=- shape=80310a19 vocab=de684bbb
-/
theorem smallOddPart_squarefree (B n : ℕ) :
    Squarefree (smallOddPart B n) := by
  rw [smallOddPart]
  exact squarefree_prod_primes _ fun p hp ↦
    (prime_and_small_of_mem_smallOddPrimeSupport hp).1

/-- The large odd kernel divides the original integer.
@isnad1 id=dvd.0h2v.s3.bf838bf47eb3 from=translated src=- shape=bf83e09e vocab=a31e5844
-/
theorem largeOddKernel_dvd (B n : ℕ) :
    largeOddKernel B n ∣ n := by
  rw [largeOddKernel]
  apply Finset.prod_primes_dvd n
  · intro p hp
    exact (prime_and_large_of_mem_largeOddPrimeSupport hp).1.prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors
      (largeOddPrimeSupport_subset_primeFactors B n hp)

/-- The complementary small odd part also divides the original integer.
@isnad1 id=dvd.0h2v.s3.27f50b847878 from=translated src=- shape=bf83e09e vocab=4d35a07e
-/
theorem smallOddPart_dvd (B n : ℕ) :
    smallOddPart B n ∣ n := by
  rw [smallOddPart]
  apply Finset.prod_primes_dvd n
  · intro p hp
    exact (prime_and_small_of_mem_smallOddPrimeSupport hp).1.prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors
      (smallOddPrimeSupport_subset_primeFactors B n hp)

/-- Positivity of the large odd kernel in inequality form.
@isnad1 id=le.0h2v.s3.db60befd6b85 from=translated src=- shape=a120b2a8 vocab=a20433a2
-/
theorem one_le_largeOddKernel (B n : ℕ) :
    1 ≤ largeOddKernel B n :=
  Nat.one_le_iff_ne_zero.mpr (largeOddKernel_ne_zero B n)

/-- A positive integer bounds its large odd kernel.
@isnad1 id=le.1h2v.s4.c75b8b2e6291 from=translated src=- shape=c70c600f vocab=c4eee156
-/
theorem largeOddKernel_le {B n : ℕ} (hn : 0 < n) :
    largeOddKernel B n ≤ n :=
  Nat.le_of_dvd hn (largeOddKernel_dvd B n)

/-- The exact interval needed in the counting argument.
@isnad1 id=mem.1h2v.s5.7ea673dabfa2 from=translated src=- shape=ad717d7a vocab=668bbbcd
-/
theorem largeOddKernel_mem_Icc {B n : ℕ} (hn : 0 < n) :
    largeOddKernel B n ∈ Finset.Icc 1 n := by
  exact Finset.mem_Icc.mpr ⟨one_le_largeOddKernel B n, largeOddKernel_le hn⟩

/-- The distinct-prime-factor count of the kernel is its support cardinality.
@isnad1 id=eq.0h2v.s4.f486eb4a5bb0 from=translated src=- shape=b024c3ab vocab=44c19a00
-/
theorem cardDistinctFactors_largeOddKernel (B n : ℕ) :
    ArithmeticFunction.cardDistinctFactors (largeOddKernel B n) =
      (largeOddPrimeSupport B n).card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  change (largeOddKernel B n).primeFactors.card =
    (largeOddPrimeSupport B n).card
  rw [primeFactors_largeOddKernel]

/-! ## The small/large partition and canonical decomposition -/

/-- The small and large odd supports are disjoint.
@isnad1 id=disjoint.0h2v.s4.8c3ac761668a from=translated src=- shape=12c10d9c vocab=4cd851a4
-/
theorem disjoint_smallOddPrimeSupport_largeOddPrimeSupport (B n : ℕ) :
    Disjoint (smallOddPrimeSupport B n) (largeOddPrimeSupport B n) := by
  rw [Finset.disjoint_left]
  intro p hpSmall hpLarge
  exact (Nat.not_lt_of_ge
    (prime_and_small_of_mem_smallOddPrimeSupport hpSmall).2)
    (prime_and_large_of_mem_largeOddPrimeSupport hpLarge).2

/-- Splitting at `B` exhausts the full odd-prime support.
@isnad1 id=eq.0h2v.s4.41ebeb448507 from=translated src=- shape=627de8bf vocab=eb9d26a7
-/
theorem smallOddPrimeSupport_union_largeOddPrimeSupport (B n : ℕ) :
    smallOddPrimeSupport B n ∪ largeOddPrimeSupport B n =
      oddPrimeSupport n := by
  ext p
  simp only [Finset.mem_union, mem_smallOddPrimeSupport,
    mem_largeOddPrimeSupport]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    exact (le_or_gt p B).elim
      (fun hpB ↦ Or.inl ⟨hp, hpB⟩)
      (fun hpB ↦ Or.inr ⟨hp, hpB⟩)

/-- The products of the two pieces multiply back to the full odd part.
@isnad1 id=eq.0h2v.s4.53566e92c2de from=translated src=- shape=4740f01e vocab=9869f958
-/
theorem smallOddPart_mul_largeOddKernel (B n : ℕ) :
    smallOddPart B n * largeOddKernel B n =
      (oddPrimeSupport n).prod id := by
  rw [smallOddPart, largeOddKernel,
    ← Finset.prod_union
      (disjoint_smallOddPrimeSupport_largeOddPrimeSupport B n),
    smallOddPrimeSupport_union_largeOddPrimeSupport]

/-- The small and large odd parts have disjoint prime support.
@isnad1 id=coprime.0h2v.s3.b6e533ff911e from=translated src=- shape=f4bb34bc vocab=1e2f992a
-/
theorem smallOddPart_coprime_largeOddKernel (B n : ℕ) :
    (smallOddPart B n).Coprime (largeOddKernel B n) := by
  rw [smallOddPart, largeOddKernel]
  apply Nat.Coprime.prod_left
  intro p hpSmall
  apply Nat.Coprime.prod_right
  intro q hqLarge
  have hpData := prime_and_small_of_mem_smallOddPrimeSupport hpSmall
  have hqData := prime_and_large_of_mem_largeOddPrimeSupport hqLarge
  apply (Nat.coprime_primes hpData.1 hqData.1).mpr
  exact Nat.ne_of_lt (hpData.2.trans_lt hqData.2)

/--
The canonical decomposition used in Lemma 4.2:

`n = a² u r`,

where `a` is the canonical square part, `u` is squarefree and supported on
primes at most `B`, and `r = largeOddKernel B n` is squarefree and supported
on primes strictly above `B`.
@isnad1 id=eq.1h2v.s5.c6cd724424a0 from=translated src=- shape=4d2cef31 vocab=b58cea5e
-/
theorem canonical_largeOddKernel_decomposition
    {B n : ℕ} (hn : n ≠ 0) :
    n = canonicalSquarePart n ^ 2 *
        smallOddPart B n * largeOddKernel B n := by
  calc
    n = (oddPrimeSupport n).prod id * canonicalSquarePart n ^ 2 :=
      canonical_odd_mul_sq_decomposition hn
    _ = (smallOddPart B n * largeOddKernel B n) *
        canonicalSquarePart n ^ 2 := by
      rw [smallOddPart_mul_largeOddKernel]
    _ = canonicalSquarePart n ^ 2 *
        smallOddPart B n * largeOddKernel B n := by
      ac_rfl

/-- The canonical square part is nonzero whenever `n` is nonzero.
@isnad1 id=ne.1h1v.s4.98677b1660fe from=translated src=- shape=5aedd577 vocab=f3775ed2
-/
theorem canonicalSquarePart_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    canonicalSquarePart n ≠ 0 := by
  intro ha
  apply hn
  rw [canonical_largeOddKernel_decomposition (B := 0) hn, ha]
  simp

/-- A prime divides the large kernel exactly when it belongs to its support.
@isnad1 id=iff.1h3v.s4.76eff4f7ac3a from=translated src=- shape=7a2ffb30 vocab=fe058e5a
-/
theorem prime_dvd_largeOddKernel_iff
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ largeOddKernel B n ↔ p ∈ largeOddPrimeSupport B n := by
  rw [← primeFactors_largeOddKernel B n,
    Nat.mem_primeFactors_of_ne_zero (largeOddKernel_ne_zero B n)]
  simp [hp]

/--
The prime divisors of the kernel are exactly the primes above `B` occurring
to odd order in `n`.
@isnad1 id=iff.1h3v.s5.fdd2de242c3b from=translated src=- shape=4c9f5efe vocab=03f81f0f
-/
theorem prime_dvd_largeOddKernel_iff_large_odd
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ largeOddKernel B n ↔
      B < p ∧ Odd (n.factorization p) := by
  rw [prime_dvd_largeOddKernel_iff hp,
    mem_largeOddPrimeSupport_iff_prime_large_odd]
  simp [hp]

/-- A prime divides the small odd part exactly when it belongs to its support.
@isnad1 id=iff.1h3v.s4.cf549b542d38 from=translated src=- shape=7a2ffb30 vocab=d454c8fe
-/
theorem prime_dvd_smallOddPart_iff
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ smallOddPart B n ↔ p ∈ smallOddPrimeSupport B n := by
  rw [← primeFactors_smallOddPart B n,
    Nat.mem_primeFactors_of_ne_zero (smallOddPart_ne_zero B n)]
  simp [hp]

/--
The prime divisors of the small odd part are exactly the odd-valuation primes
at or below `B`.
@isnad1 id=iff.1h3v.s5.eb07a4481560 from=translated src=- shape=e8d72db9 vocab=6830001f
-/
theorem prime_dvd_smallOddPart_iff_small_odd
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ smallOddPart B n ↔
      p ≤ B ∧ Odd (n.factorization p) := by
  rw [prime_dvd_smallOddPart_iff hp,
    mem_smallOddPrimeSupport_iff_prime_small_odd]
  simp [hp]

/-- Explicit factorization of the large kernel: every retained exponent is one.
@isnad1 id=eq.0h3v.s5.df0d6b04b24f from=translated src=- shape=5530f6d6 vocab=b255acab
-/
theorem factorization_largeOddKernel (B n p : ℕ) :
    (largeOddKernel B n).factorization p =
      if p ∈ largeOddPrimeSupport B n then 1 else 0 := by
  by_cases hp : p ∈ largeOddPrimeSupport B n
  · rw [ite_eq_left hp]
    exact Nat.factorization_eq_one_of_squarefree
      (largeOddKernel_squarefree B n)
      (prime_and_large_of_mem_largeOddPrimeSupport hp).1
      ((prime_dvd_largeOddKernel_iff
        (prime_and_large_of_mem_largeOddPrimeSupport hp).1).mpr hp)
  · rw [ite_eq_right hp]
    apply Finsupp.notMem_support_iff.mp
    rw [Nat.support_factorization, primeFactors_largeOddKernel]
    exact hp

/-- Explicit factorization of the small odd part.
@isnad1 id=eq.0h3v.s5.fc0f2fadab58 from=translated src=- shape=5530f6d6 vocab=dc29d64c
-/
theorem factorization_smallOddPart (B n p : ℕ) :
    (smallOddPart B n).factorization p =
      if p ∈ smallOddPrimeSupport B n then 1 else 0 := by
  by_cases hp : p ∈ smallOddPrimeSupport B n
  · rw [ite_eq_left hp]
    exact Nat.factorization_eq_one_of_squarefree
      (smallOddPart_squarefree B n)
      (prime_and_small_of_mem_smallOddPrimeSupport hp).1
      ((prime_dvd_smallOddPart_iff
        (prime_and_small_of_mem_smallOddPrimeSupport hp).1).mpr hp)
  · rw [ite_eq_right hp]
    apply Finsupp.notMem_support_iff.mp
    rw [Nat.support_factorization, primeFactors_smallOddPart]
    exact hp

/-- The kernel is one exactly when its defining support is empty.
@isnad1 id=iff.0h2v.s4.a82830d9fb98 from=translated src=- shape=23f09db3 vocab=c4fc0a74
-/
theorem largeOddKernel_eq_one_iff_support_eq_empty (B n : ℕ) :
    largeOddKernel B n = 1 ↔ largeOddPrimeSupport B n = ∅ := by
  constructor
  · intro hk
    have hs := primeFactors_largeOddKernel B n
    rw [hk] at hs
    simpa using hs.symm
  · intro hs
    simp [largeOddKernel, hs]

/--
The intrinsic defect predicate is equivalently the assertion that the large
odd kernel is one.
@isnad1 id=iff.0h2v.s4.0226406410bf from=translated src=- shape=1e870c3c vocab=d0722aac
-/
theorem largeOddKernel_eq_one_iff_hDefective (B n : ℕ) :
    largeOddKernel B n = 1 ↔ HDefective B n := by
  rw [largeOddKernel_eq_one_iff_support_eq_empty]
  constructor
  · intro hs p hpPrime hpB
    by_contra hpParity
    have hpMem :=
      (parityVec_ne_zero_iff_mem_largeOddPrimeSupport hpPrime hpB).mp hpParity
    rw [hs] at hpMem
    exact Finset.notMem_empty p hpMem
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hpMem
    have hpData := prime_and_large_of_mem_largeOddPrimeSupport hpMem
    exact (mem_largeOddPrimeSupport_iff.mp hpMem).2
      (h p hpData.1 hpData.2)

end LargeOddKernel
end PaperC
