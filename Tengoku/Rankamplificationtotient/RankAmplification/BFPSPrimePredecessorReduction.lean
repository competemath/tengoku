import Tengoku.Rankamplificationtotient.RankAmplification.BFPSRankin
import Tengoku.Rankamplificationtotient.RankAmplification.AffineSelbergReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite BFPS smooth-predecessor reduction This file formalizes the finite decomposition used in Pomerance--Shparlinski Theorem 1 and subsequently quoted as BFPS Lemma 2.2. -/

namespace RankAmplification

open Finset
open scoped BigOperators Nat.Prime

noncomputable section

/-! ## Largest-prime-factor shells -/

/-- Primes `p ≤ X` whose predecessor is `hi`-smooth but whose largest prime factor exceeds `lo`.-/
def smoothPredecessorPrimeShell (X lo hi : ℕ) : Finset ℕ :=
  (smoothPredecessorPrimeSet X hi).filter fun p ↦
    lo < largestPrimeFactor (p - 1)

@[simp]
theorem mem_smoothPredecessorPrimeShell {X lo hi p : ℕ} :
    p ∈ smoothPredecessorPrimeShell X lo hi ↔
      p.Prime ∧ p ≤ X ∧ IsSmooth hi (p - 1) ∧
        lo < largestPrimeFactor (p - 1) := by
  classical
  simp only [smoothPredecessorPrimeShell, Finset.mem_filter,
    mem_smoothPredecessorPrimeSet]
  aesop

/-- Exact shell identity: the difference of two smooth-predecessor prime sets is the largest-prime-factor shell between their cutoffs.-/
theorem smoothPredecessorPrimeSet_sdiff_eq_shell {X lo hi : ℕ}
    (hlo : 1 ≤ lo) :
    smoothPredecessorPrimeSet X hi \ smoothPredecessorPrimeSet X lo =
      smoothPredecessorPrimeShell X lo hi := by
  classical
  ext p
  constructor
  · intro hp
    have hpDiff := Finset.mem_sdiff.mp hp
    have hpHi := mem_smoothPredecessorPrimeSet.mp hpDiff.1
    have hpred : p - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpHi.1.one_lt)
    have hnotLe : ¬largestPrimeFactor (p - 1) ≤ lo := by
      intro hle
      have hsmoothLo : IsSmooth lo (p - 1) :=
        (isSmooth_iff_largestPrimeFactor_le hlo hpred).mpr hle
      exact hpDiff.2 (mem_smoothPredecessorPrimeSet.mpr
        ⟨hpHi.1, hpHi.2.1, hsmoothLo⟩)
    exact mem_smoothPredecessorPrimeShell.mpr
      ⟨hpHi.1, hpHi.2.1, hpHi.2.2, Nat.lt_of_not_ge hnotLe⟩
  · intro hp
    have hpShell := mem_smoothPredecessorPrimeShell.mp hp
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_smoothPredecessorPrimeSet.mpr
      ⟨hpShell.1, hpShell.2.1, hpShell.2.2.1⟩, ?_⟩
    intro hpLo
    have hsmoothLo := (mem_smoothPredecessorPrimeSet.mp hpLo).2.2
    have hle := largestPrimeFactor_le_of_isSmooth hlo hsmoothLo
    exact (Nat.not_lt_of_ge hle) hpShell.2.2.2

/-- Smooth-predecessor prime sets are monotone in the smoothness cutoff.-/
theorem smoothPredecessorPrimeSet_subset_of_le {X lo hi : ℕ} (hlohi : lo ≤ hi) :
    smoothPredecessorPrimeSet X lo ⊆ smoothPredecessorPrimeSet X hi := by
  intro p hp
  have hpData := mem_smoothPredecessorPrimeSet.mp hp
  apply mem_smoothPredecessorPrimeSet.mpr
  refine ⟨hpData.1, hpData.2.1, hpData.2.2.1, ?_⟩
  intro r hr
  exact (hpData.2.2.2 r hr).trans hlohi

/-- Exact cardinal grouping into the lower cutoff and one bounded shell.-/
theorem card_smoothPredecessorPrimeSet_eq_add_shell {X lo hi : ℕ}
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    (smoothPredecessorPrimeSet X hi).card =
      (smoothPredecessorPrimeSet X lo).card +
        (smoothPredecessorPrimeShell X lo hi).card := by
  have hcard := Finset.card_sdiff_add_card_eq_card
    (smoothPredecessorPrimeSet_subset_of_le (X := X) hlohi)
  rw [smoothPredecessorPrimeSet_sdiff_eq_shell hlo] at hcard
  omega

/-- The largest prime factor selected from a predecessor shell.-/
def predecessorShellPrime (p : ℕ) : ℕ := largestPrimeFactor (p - 1)

/-- The complementary multiplier `m = (p-1)/P⁺(p-1)`.-/
def predecessorShellMultiplier (p : ℕ) : ℕ :=
  (p - 1) / predecessorShellPrime p

theorem predecessorShellPrime_prime {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    (predecessorShellPrime p).Prime := by
  apply largestPrimeFactor_prime
  exact hlo.trans_lt (mem_smoothPredecessorPrimeShell.mp hp).2.2.2

theorem predecessorShellPrime_dvd_pred {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    predecessorShellPrime p ∣ p - 1 := by
  apply largestPrimeFactor_dvd
  exact hlo.trans_lt (mem_smoothPredecessorPrimeShell.mp hp).2.2.2

/-- Exact predecessor factorization.-/
theorem predecessorShellMultiplier_mul_prime {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    predecessorShellMultiplier p * predecessorShellPrime p = p - 1 := by
  exact Nat.div_mul_cancel (predecessorShellPrime_dvd_pred hlo hp)

/-- Exact affine reconstruction `p = m q + 1`.-/
theorem predecessor_eq_multiplier_mul_prime_add_one {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    p = predecessorShellMultiplier p * predecessorShellPrime p + 1 := by
  rw [predecessorShellMultiplier_mul_prime hlo hp]
  exact (Nat.sub_add_cancel (mem_smoothPredecessorPrimeShell.mp hp).1.one_le).symm

theorem predecessorShellMultiplier_pos {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    0 < predecessorShellMultiplier p := by
  have hprodPos : 0 < p - 1 :=
    Nat.sub_pos_of_lt (mem_smoothPredecessorPrimeShell.mp hp).1.one_lt
  rw [← predecessorShellMultiplier_mul_prime hlo hp] at hprodPos
  exact pos_of_mul_pos_left hprodPos (Nat.zero_le _)

/-- The complementary multiplier remains smooth at the shell's upper endpoint.-/
theorem predecessorShellMultiplier_smooth {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    IsSmooth hi (predecessorShellMultiplier p) := by
  have hfactor := predecessorShellMultiplier_mul_prime hlo hp
  apply (mem_smoothPredecessorPrimeShell.mp hp).2.2.1.of_dvd
  · exact ⟨predecessorShellPrime p, hfactor.symm⟩
  · exact (predecessorShellMultiplier_pos hlo hp).ne'

/-- Maximality of `q=P⁺(p-1)` gives the stronger fact that every prime factor of `m` is at most `q` itself.-/
theorem predecessorShellMultiplier_smooth_at_shellPrime {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    IsSmooth (predecessorShellPrime p) (predecessorShellMultiplier p) := by
  refine ⟨(predecessorShellMultiplier_pos hlo hp).ne', ?_⟩
  intro r hr
  have hrPrime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hrDvdMultiplier : r ∣ predecessorShellMultiplier p :=
    Nat.dvd_of_mem_primeFactors hr
  have hmultiplierDvd : predecessorShellMultiplier p ∣ p - 1 :=
    ⟨predecessorShellPrime p, (predecessorShellMultiplier_mul_prime hlo hp).symm⟩
  exact prime_le_largestPrimeFactor hrPrime
    (Nat.ne_of_gt (Nat.sub_pos_of_lt (mem_smoothPredecessorPrimeShell.mp hp).1.one_lt))
    (hrDvdMultiplier.trans hmultiplierDvd)

/-- The shell prime is at most its upper endpoint.-/
theorem predecessorShellPrime_le {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    predecessorShellPrime p ≤ hi := by
  exact (mem_smoothPredecessorPrimeShell.mp hp).2.2.1.2
    (predecessorShellPrime p)
    (largestPrimeFactor_mem_primeFactors
      (hlo.trans_lt (mem_smoothPredecessorPrimeShell.mp hp).2.2.2))

/-- The complementary multiplier has the uniform shell bound `m ≤ X/(lo+1)`.-/
theorem predecessorShellMultiplier_le {X lo hi p : ℕ} (hlo : 1 ≤ lo)
    (hp : p ∈ smoothPredecessorPrimeShell X lo hi) :
    predecessorShellMultiplier p ≤ X / (lo + 1) := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < lo + 1)]
  have hqLower : lo + 1 ≤ predecessorShellPrime p :=
    Nat.succ_le_iff.mpr (mem_smoothPredecessorPrimeShell.mp hp).2.2.2
  calc
    predecessorShellMultiplier p * (lo + 1) ≤
        predecessorShellMultiplier p * predecessorShellPrime p :=
      Nat.mul_le_mul_left _ hqLower
    _ = p - 1 := predecessorShellMultiplier_mul_prime hlo hp
    _ ≤ p := Nat.sub_le p 1
    _ ≤ X := (mem_smoothPredecessorPrimeShell.mp hp).2.1

/-! ## Finite reindexing by `(m,q)` -/

/-- For fixed `m`, the bounded one-or-two-affine prime problem `q`, `m q + 1`.-/
def bfpsAffinePrimeSet (m lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter fun q ↦ q.Prime ∧ (m * q + 1).Prime

@[simp]
theorem mem_bfpsAffinePrimeSet {m lo hi q : ℕ} :
    q ∈ bfpsAffinePrimeSet m lo hi ↔
      lo < q ∧ q ≤ hi ∧ q.Prime ∧ (m * q + 1).Prime := by
  simp [bfpsAffinePrimeSet, and_assoc]

/-- Smooth multipliers allowed by the shell factorization.-/
noncomputable def bfpsSmoothMultiplierSet (X Y lo : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (X / (lo + 1))).filter fun m ↦ IsSmooth Y m

@[simp]
theorem mem_bfpsSmoothMultiplierSet {X Y lo m : ℕ} :
    m ∈ bfpsSmoothMultiplierSet X Y lo ↔
      1 ≤ m ∧ m ≤ X / (lo + 1) ∧ IsSmooth Y m := by
  classical
  simp only [bfpsSmoothMultiplierSet, Finset.mem_filter, Finset.mem_Icc,
    and_assoc]

/-- The finite target of the largest-prime-factor encoding.-/
def bfpsPredecessorShellPairSet (X lo hi : ℕ) : Finset (Σ _m : ℕ, ℕ) :=
  (bfpsSmoothMultiplierSet X hi lo).sigma fun m ↦ bfpsAffinePrimeSet m lo hi

@[simp]
theorem mem_bfpsPredecessorShellPairSet {X lo hi : ℕ} {z : Σ _m : ℕ, ℕ} :
    z ∈ bfpsPredecessorShellPairSet X lo hi ↔
      z.1 ∈ bfpsSmoothMultiplierSet X hi lo ∧
        z.2 ∈ bfpsAffinePrimeSet z.1 lo hi := by
  simp [bfpsPredecessorShellPairSet]

/-- The shell injects into the finite family of affine prime problems indexed by smooth `m`.-/
theorem card_smoothPredecessorPrimeShell_le_pairSet {X lo hi : ℕ} (hlo : 1 ≤ lo) :
    (smoothPredecessorPrimeShell X lo hi).card ≤
      (bfpsPredecessorShellPairSet X lo hi).card := by
  classical
  let encode : ℕ → (Σ _m : ℕ, ℕ) := fun p ↦
    ⟨predecessorShellMultiplier p, predecessorShellPrime p⟩
  apply Finset.card_le_card_of_injOn encode
  · intro p hp
    apply mem_bfpsPredecessorShellPairSet.mpr
    constructor
    · exact mem_bfpsSmoothMultiplierSet.mpr
        ⟨predecessorShellMultiplier_pos hlo hp,
          predecessorShellMultiplier_le hlo hp,
          predecessorShellMultiplier_smooth hlo hp⟩
    · apply mem_bfpsAffinePrimeSet.mpr
      exact ⟨(mem_smoothPredecessorPrimeShell.mp hp).2.2.2,
        predecessorShellPrime_le hlo hp,
        predecessorShellPrime_prime hlo hp,
        (predecessor_eq_multiplier_mul_prime_add_one hlo hp) ▸
          (mem_smoothPredecessorPrimeShell.mp hp).1⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    have hm : predecessorShellMultiplier p₁ = predecessorShellMultiplier p₂ :=
      congrArg Sigma.fst heq
    have hq : predecessorShellPrime p₁ = predecessorShellPrime p₂ :=
      congrArg (fun z : Σ _m : ℕ, ℕ ↦ z.2) heq
    calc
      p₁ = predecessorShellMultiplier p₁ * predecessorShellPrime p₁ + 1 :=
        predecessor_eq_multiplier_mul_prime_add_one hlo hp₁
      _ = predecessorShellMultiplier p₂ * predecessorShellPrime p₂ + 1 := by
        rw [hm, hq]
      _ = p₂ := (predecessor_eq_multiplier_mul_prime_add_one hlo hp₂).symm

/-- Cardinal form of the exact reduction to a smooth-multiplier sum.-/
theorem card_smoothPredecessorPrimeShell_le_sum_affine {X lo hi : ℕ} (hlo : 1 ≤ lo) :
    (smoothPredecessorPrimeShell X lo hi).card ≤
      ∑ m ∈ bfpsSmoothMultiplierSet X hi lo, (bfpsAffinePrimeSet m lo hi).card := by
  exact (card_smoothPredecessorPrimeShell_le_pairSet hlo).trans_eq
    (Finset.card_sigma (bfpsSmoothMultiplierSet X hi lo)
      (fun m ↦ bfpsAffinePrimeSet m lo hi))

/-! ## The one-affine exception and the two-affine endpoint -/

/-- If both `q` and `q+1` are prime, then `q=2`.-/
theorem eq_two_of_mem_bfpsAffinePrimeSet_one {lo hi q : ℕ}
    (hq : q ∈ bfpsAffinePrimeSet 1 lo hi) : q = 2 := by
  have hdata := mem_bfpsAffinePrimeSet.mp hq
  rcases hdata.2.2.1.eq_two_or_odd' with hqTwo | hqOdd
  · exact hqTwo
  · have hsuccPrime : (q + 1).Prime := by simpa using hdata.2.2.2
    have hsuccTwo : q + 1 = 2 := hsuccPrime.even_iff.mp hqOdd.add_one
    have hqOne : q = 1 := by omega
    subst q
    exact (Nat.not_prime_one hdata.2.2.1).elim

/-- The degenerate one-affine contribution contains at most one prime.-/
theorem card_bfpsAffinePrimeSet_one_le (lo hi : ℕ) :
    (bfpsAffinePrimeSet 1 lo hi).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q₁ hq₁ q₂ hq₂
  rw [eq_two_of_mem_bfpsAffinePrimeSet_one hq₁,
    eq_two_of_mem_bfpsAffinePrimeSet_one hq₂]

/-- Nontrivial smooth multipliers, for which the pair `q`, `m q+1` is genuinely two-affine.-/
def bfpsNontrivialSmoothMultiplierSet (X Y lo : ℕ) : Finset ℕ :=
  (bfpsSmoothMultiplierSet X Y lo).filter fun m ↦ 2 ≤ m

@[simp]
theorem mem_bfpsNontrivialSmoothMultiplierSet {X Y lo m : ℕ} :
    m ∈ bfpsNontrivialSmoothMultiplierSet X Y lo ↔
      2 ≤ m ∧ m ≤ X / (lo + 1) ∧ IsSmooth Y m := by
  classical
  simp only [bfpsNontrivialSmoothMultiplierSet, Finset.mem_filter,
    mem_bfpsSmoothMultiplierSet]
  constructor
  · rintro ⟨⟨_hmOne, hmBound, hmSmooth⟩, hmTwo⟩
    exact ⟨hmTwo, hmBound, hmSmooth⟩
  · rintro ⟨hmTwo, hmBound, hmSmooth⟩
    exact ⟨⟨by omega, hmBound, hmSmooth⟩, hmTwo⟩

/-- The exact weighted smooth-multiplier sum appearing after Brun--Selberg sieving.-/
def bfpsWeightedSmoothMultiplierSum (X Y lo : ℕ) : ℝ :=
  ∑ m ∈ bfpsNontrivialSmoothMultiplierSet X Y lo,
    (m : ℝ) / (m.totient : ℝ)

theorem bfpsWeightedSmoothMultiplierSum_nonneg (X Y lo : ℕ) :
    0 ≤ bfpsWeightedSmoothMultiplierSum X Y lo := by
  apply Finset.sum_nonneg
  intro m _
  positivity

/-- The finite smooth-multiplier sum splits into the single `m=1` exception and `m≥2`.-/
theorem sum_card_bfpsAffinePrimeSet_le_one_add_nontrivial (X lo hi : ℕ) :
    (∑ m ∈ bfpsSmoothMultiplierSet X hi lo,
      (bfpsAffinePrimeSet m lo hi).card) ≤
      1 + ∑ m ∈ bfpsNontrivialSmoothMultiplierSet X hi lo,
        (bfpsAffinePrimeSet m lo hi).card := by
  classical
  let S := bfpsSmoothMultiplierSet X hi lo
  let f : ℕ → ℕ := fun m ↦ (bfpsAffinePrimeSet m lo hi).card
  have hsmallSubset : S.filter (fun m ↦ ¬2 ≤ m) ⊆ ({1} : Finset ℕ) := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmOne : m = 1 := by
      have hmLower := (mem_bfpsSmoothMultiplierSet.mp hmData.1).1
      omega
    simp [hmOne]
  have hsmall : (∑ m ∈ S.filter (fun m ↦ ¬2 ≤ m), f m) ≤ 1 := by
    calc
      (∑ m ∈ S.filter (fun m ↦ ¬2 ≤ m), f m) ≤
          ∑ m ∈ ({1} : Finset ℕ), f m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsmallSubset
        intro m _ _
        omega
      _ = f 1 := by simp
      _ ≤ 1 := card_bfpsAffinePrimeSet_one_le lo hi
  have hpartition := Finset.sum_filter_add_sum_filter_not S (fun m ↦ 2 ≤ m) f
  change (∑ m ∈ S, f m) ≤
    1 + ∑ m ∈ S.filter (fun m ↦ 2 ≤ m), f m
  rw [← hpartition]
  omega

/-- The shell count after removing the one-affine exception, still entirely finite.-/
theorem card_smoothPredecessorPrimeShell_cast_le_one_add_nontrivial
    {X lo hi : ℕ} (hlo : 1 ≤ lo) :
    ((smoothPredecessorPrimeShell X lo hi).card : ℝ) ≤
      1 + ∑ m ∈ bfpsNontrivialSmoothMultiplierSet X hi lo,
        ((bfpsAffinePrimeSet m lo hi).card : ℝ) := by
  have h := (card_smoothPredecessorPrimeShell_le_sum_affine hlo).trans
    (sum_card_bfpsAffinePrimeSet_le_one_add_nontrivial X lo hi)
  exact_mod_cast h

/-- Terminal Brun--Selberg input for the genuinely two-affine pairs.-/
def bfpsLogSquaredScale (R : ℕ) : ℝ :=
  AffinePrimePair.logSquaredScale R

/-- Uniform terminal sieve bound for the genuinely two-affine predecessor-prime pairs.-/
def HasBFPSTwoAffineSieveBound (C : ℝ) : Prop :=
  ∀ m lo hi, 2 ≤ m → lo < hi → 3 ≤ hi →
    ((bfpsAffinePrimeSet m lo hi).card : ℝ) ≤
      C * bfpsLogSquaredScale hi * ((m : ℝ) / (m.totient : ℝ))

/-- Kernel-checked shell reduction to the terminal two-affine estimate and the weighted smooth-m sum.-/
theorem card_smoothPredecessorPrimeShell_cast_le_weighted
    {X lo hi : ℕ} {C : ℝ}
    (hlo : 1 ≤ lo) (hlohi : lo < hi) (hhi : 3 ≤ hi)
    (hsieve : HasBFPSTwoAffineSieveBound C) :
    ((smoothPredecessorPrimeShell X lo hi).card : ℝ) ≤
      1 + C * bfpsLogSquaredScale hi * bfpsWeightedSmoothMultiplierSum X hi lo := by
  calc
    ((smoothPredecessorPrimeShell X lo hi).card : ℝ) ≤
        1 + ∑ m ∈ bfpsNontrivialSmoothMultiplierSet X hi lo,
          ((bfpsAffinePrimeSet m lo hi).card : ℝ) :=
      card_smoothPredecessorPrimeShell_cast_le_one_add_nontrivial hlo
    _ ≤ 1 + ∑ m ∈ bfpsNontrivialSmoothMultiplierSet X hi lo,
        C * bfpsLogSquaredScale hi * ((m : ℝ) / (m.totient : ℝ)) := by
      apply add_le_add (le_refl 1)
      apply Finset.sum_le_sum
      intro m hm
      exact hsieve m lo hi
        (mem_bfpsNontrivialSmoothMultiplierSet.mp hm).1 hlohi hhi
    _ = 1 + C * bfpsLogSquaredScale hi * bfpsWeightedSmoothMultiplierSum X hi lo := by
      rw [bfpsWeightedSmoothMultiplierSum, Finset.mul_sum]

/-- The remaining smooth-number input, parameterized by an arbitrary explicit majorant.-/
def HasBFPSWeightedSmoothMultiplierBound (majorant : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ X Y lo,
    bfpsWeightedSmoothMultiplierSum X Y lo ≤ majorant X Y lo

theorem bfpsLogSquaredScale_nonneg (R : ℕ) : 0 ≤ bfpsLogSquaredScale R := by
  unfold bfpsLogSquaredScale AffinePrimePair.logSquaredScale
  positivity

/-- Complete bounded-shell estimate from the two named terminal inputs.-/
theorem card_smoothPredecessorPrimeShell_cast_le_majorant
    {X lo hi : ℕ} {C : ℝ} {majorant : ℕ → ℕ → ℕ → ℝ}
    (hlo : 1 ≤ lo) (hlohi : lo < hi) (hhi : 3 ≤ hi) (hC : 0 ≤ C)
    (hsieve : HasBFPSTwoAffineSieveBound C)
    (hsmooth : HasBFPSWeightedSmoothMultiplierBound majorant) :
    ((smoothPredecessorPrimeShell X lo hi).card : ℝ) ≤
      1 + C * bfpsLogSquaredScale hi * majorant X hi lo := by
  calc
    ((smoothPredecessorPrimeShell X lo hi).card : ℝ) ≤
        1 + C * bfpsLogSquaredScale hi * bfpsWeightedSmoothMultiplierSum X hi lo :=
      card_smoothPredecessorPrimeShell_cast_le_weighted hlo hlohi hhi hsieve
    _ ≤ 1 + C * bfpsLogSquaredScale hi * majorant X hi lo := by
      exact add_le_add (le_refl 1) <|
        mul_le_mul_of_nonneg_left (hsmooth X hi lo)
          (mul_nonneg hC (bfpsLogSquaredScale_nonneg hi))

/-- The same result written directly for the difference `π(X,hi)-π(X,lo)`.-/
theorem card_smoothPredecessorPrimeSet_sdiff_cast_le_majorant
    {X lo hi : ℕ} {C : ℝ} {majorant : ℕ → ℕ → ℕ → ℝ}
    (hlo : 1 ≤ lo) (hlohi : lo < hi) (hhi : 3 ≤ hi) (hC : 0 ≤ C)
    (hsieve : HasBFPSTwoAffineSieveBound C)
    (hsmooth : HasBFPSWeightedSmoothMultiplierBound majorant) :
    (((smoothPredecessorPrimeSet X hi \ smoothPredecessorPrimeSet X lo).card : ℕ) : ℝ) ≤
      1 + C * bfpsLogSquaredScale hi * majorant X hi lo := by
  rw [smoothPredecessorPrimeSet_sdiff_eq_shell hlo]
  exact card_smoothPredecessorPrimeShell_cast_le_majorant
    hlo hlohi hhi hC hsieve hsmooth

end

end RankAmplification
