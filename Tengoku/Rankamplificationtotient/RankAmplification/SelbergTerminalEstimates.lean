import Tengoku.Rankamplificationtotient.RankAmplification.SelbergFundamentalLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Terminal estimates for the finite Selberg minimizer This module first closes the two residual Selberg propositions for an unconditional bounded cutoff. -/

namespace RankAmplification

open Finset Nat ArithmeticFunction
open scoped BigOperators Nat.Prime ArithmeticFunction.Moebius

noncomputable section

namespace BFPSTwoAffine

/-! ## A completely unconditional base cutoff -/

/-- The constant-one cutoff.-/
def unitCutoff (_R : ℕ) : ℕ := 1

/--
@isnad1 id=eq.0h1v.s3.340188134499 from=translated src=- shape=b14ee516 vocab=259244c5
-/
@[simp]
theorem unitCutoff_apply (R : ℕ) : unitCutoff R = 1 := rfl

/--
@isnad1 id=eq.0h0v.s3.927c01d94672 from=translated src=- shape=3c26ae4f vocab=35f16702
-/
@[simp]
theorem primeProduct_one : primeProduct 1 = 1 := by
  simp [primeProduct, Nat.primesLE]

/--
@isnad1 id=eq.0h1v.s4.5aadc635822f from=translated src=- shape=8fc7241c vocab=7efc64f0
-/
@[simp]
theorem localSieveProduct_one (m : ℕ) : localSieveProduct m 1 = 1 := by
  simp [localSieveProduct, Nat.primesLE]

/--
@isnad1 id=eq.1h2v.s4.7acd41b7ea65 from=translated src=- shape=f4387a6b vocab=9a7ee8f4
-/
@[simp]
theorem unitSelberg_prodPrimes (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 1 hm).prodPrimes = 1 := by
  rfl

/--
@isnad1 id=eq.1h2v.s4.85b5b607d298 from=translated src=- shape=33942627 vocab=5d308fa9
-/
@[simp, nolint simpNF]
theorem unitSelberg_level (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 1 hm).level = 1 := by
  rw [minimizingSelbergSieve_level_of_one_le hm (by norm_num : 1 ≤ 1)]
  norm_num

/--
@isnad1 id=eq.1h2v.s5.2b87e8b804bc from=translated src=- shape=31aad433 vocab=389f4544
-/
theorem unitSelberg_truncatedDivisors (m R : ℕ) (hm : Even m) :
    SelbergFundamental.truncatedDivisors
      (minimizingSelbergSieve m R 1 hm) = {1} := by
  ext d
  simp [SelbergFundamental.mem_truncatedDivisors]
  omega

/--
@isnad1 id=eq.1h2v.s4.a0cc6ff5974b from=translated src=- shape=33942627 vocab=58c0fea2
-/
@[simp]
theorem unitSelberg_truncatedMass (m R : ℕ) (hm : Even m) :
    SelbergFundamental.truncatedMass
      (minimizingSelbergSieve m R 1 hm) = 1 := by
  rw [SelbergFundamental.truncatedMass, unitSelberg_truncatedDivisors]
  simp

/--
@isnad1 id=truncate.0h0v.s3.9ecbf29c7ce4 from=translated src=- shape=aa0f4b0e vocab=263ddfb5
-/
theorem truncatedMassLocalProductUpperBound_unitCutoff :
    TruncatedMassLocalProductUpperBound unitCutoff 1 := by
  intro m R _hm hmEven _hR
  simp

/--
@isnad1 id=eq.1h2v.s5.541e7a0313d7 from=translated src=- shape=456d5a5e vocab=304340b1
-/
theorem unitSelberg_rem_one (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 1 hm).rem 1 = 0 := by
  change (boundingSieve m R 1 hm).rem 1 = 0
  rw [boundingSieve_rem_eq_excess_sub_fraction hm (by norm_num)
    (by simp : Squarefree 1)]
  have hmod : R % 1 = 0 := Nat.mod_one R
  simp [residueExcessCount, hmod]

/--
@isnad1 id=eq.1h2v.s4.b94b212b9346 from=translated src=- shape=e3f50372 vocab=14a24aa3
-/
@[simp]
theorem unitSelberg_remainderMajorant (m R : ℕ) (hm : Even m) :
    minimizingWeightRemainderMajorant m R 1 hm = 1 := by
  unfold minimizingWeightRemainderMajorant
  change (∑ d ∈ (minimizingSelbergSieve m R 1 hm).prodPrimes.divisors,
      if (d : ℝ) ≤ (minimizingSelbergSieve m R 1 hm).level then
        |BoundingSieve.lambdaSquared
            (SelbergFundamental.minimizingWeight
              (minimizingSelbergSieve m R 1 hm)) d| *
          ((2 ^ d.primeFactors.card : ℕ) : ℝ)
      else 0) = 1
  rw [show (minimizingSelbergSieve m R 1 hm).prodPrimes.divisors = {1} by simp]
  simp [BoundingSieve.lambdaSquared, SelbergFundamental.minimizingWeight_one]

/--
@isnad1 id=combinat.0h0v.s3.a5abbbaace96 from=translated src=- shape=aa0f4b0e vocab=81e746dd
-/
theorem combinatorialRemainderLocalProductUpperBound_unitCutoff :
    CombinatorialRemainderLocalProductUpperBound unitCutoff 1 := by
  intro m R _hm hmEven hR
  rw [unitCutoff_apply, unitSelberg_remainderMajorant, localSieveProduct_one]
  norm_num
  exact_mod_cast (by omega : 1 ≤ R)

/--
@isnad1 id=eq.1h2v.s4.199a22b883f0 from=translated src=- shape=33942627 vocab=e9f0aa02
-/
theorem unitSelberg_levelRestrictedRemainder (m R : ℕ) (hm : Even m) :
    SelbergFundamental.levelRestrictedRemainder
      (minimizingSelbergSieve m R 1 hm) = 0 := by
  unfold SelbergFundamental.levelRestrictedRemainder
  rw [show (minimizingSelbergSieve m R 1 hm).prodPrimes.divisors = {1} by simp]
  simp only [sum_singleton, unitSelberg_level, Nat.cast_one, le_refl, ite_true]
  rw [unitSelberg_rem_one]
  simp

/--
@isnad1 id=levelres.0h0v.s3.6a76cd612163 from=translated src=- shape=aa0f4b0e vocab=66f056f2
-/
theorem levelRestrictedRemainderLocalProductUpperBound_unitCutoff :
    LevelRestrictedRemainderLocalProductUpperBound unitCutoff 0 := by
  intro m R _hm hmEven _hR
  simp [unitSelberg_levelRestrictedRemainder]

/-- Fully unconditional exact closure of the Selberg fundamental-lemma signature at cutoff one.
@isnad1 id=selbergf.0h0v.s3.5682aef860e2 from=translated src=- shape=aa0f4b0e vocab=9a91324c
-/
theorem selbergFundamentalLemmaUpperBound_unitCutoff :
    SelbergFundamentalLemmaUpperBound unitCutoff 1 := by
  simpa using selbergFundamentalLemmaUpperBound_of_mass_and_levelRestrictedRemainder
    truncatedMassLocalProductUpperBound_unitCutoff
    levelRestrictedRemainderLocalProductUpperBound_unitCutoff

/-- The route through the purely combinatorial majorant loses one harmless unit at cutoff one.
@isnad1 id=selbergf.0h0v.s3.58869c529d30 from=translated src=- shape=aa0f4b0e vocab=5fc43bc7
-/
theorem selbergFundamentalLemmaUpperBound_unitCutoff_of_combinatorial :
    SelbergFundamentalLemmaUpperBound unitCutoff 2 := by
  have h := selbergFundamentalLemmaUpperBound_of_mass_and_combinatorialRemainder
    truncatedMassLocalProductUpperBound_unitCutoff
    combinatorialRemainderLocalProductUpperBound_unitCutoff
  norm_num at h ⊢
  exact h

/-! ## Finite-exception invariance -/

/--
@isnad1 id=iff.1h3v.s5.22d57a7512fb from=translated src=- shape=b501772f vocab=b1177b8b
-/
theorem truncatedMassLocalProductUpperBound_congr
    {cutoff₁ cutoff₂ : ℕ → ℕ} {C : ℝ}
    (hcutoff : ∀ R, 3 ≤ R → cutoff₁ R = cutoff₂ R) :
    TruncatedMassLocalProductUpperBound cutoff₁ C ↔
      TruncatedMassLocalProductUpperBound cutoff₂ C := by
  constructor
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR

/--
@isnad1 id=iff.1h3v.s5.3b6de65b3da9 from=translated src=- shape=b501772f vocab=a1a10c94
-/
theorem combinatorialRemainderLocalProductUpperBound_congr
    {cutoff₁ cutoff₂ : ℕ → ℕ} {C : ℝ}
    (hcutoff : ∀ R, 3 ≤ R → cutoff₁ R = cutoff₂ R) :
    CombinatorialRemainderLocalProductUpperBound cutoff₁ C ↔
      CombinatorialRemainderLocalProductUpperBound cutoff₂ C := by
  constructor
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR

/--
@isnad1 id=iff.1h3v.s5.2dd7569cc15c from=translated src=- shape=b501772f vocab=a9fc0725
-/
theorem levelRestrictedRemainderLocalProductUpperBound_congr
    {cutoff₁ cutoff₂ : ℕ → ℕ} {C : ℝ}
    (hcutoff : ∀ R, 3 ≤ R → cutoff₁ R = cutoff₂ R) :
    LevelRestrictedRemainderLocalProductUpperBound cutoff₁ C ↔
      LevelRestrictedRemainderLocalProductUpperBound cutoff₂ C := by
  constructor
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR

/--
@isnad1 id=iff.1h3v.s5.630b66fda9d0 from=translated src=- shape=b501772f vocab=b10ba2ff
-/
theorem selbergFundamentalLemmaUpperBound_congr
    {cutoff₁ cutoff₂ : ℕ → ℕ} {C : ℝ}
    (hcutoff : ∀ R, 3 ≤ R → cutoff₁ R = cutoff₂ R) :
    SelbergFundamentalLemmaUpperBound cutoff₁ C ↔
      SelbergFundamentalLemmaUpperBound cutoff₂ C := by
  constructor
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR
  · intro h m R hm hmEven hR
    simpa [hcutoff R hR] using h m R hm hmEven hR

/-! ## The first nontrivial cutoff At cutoff two the sieve really removes the even residue class. -/

/-- The constant-two cutoff.-/
def twoCutoff (_R : ℕ) : ℕ := 2

/--
@isnad1 id=eq.0h1v.s3.231ddaa34a5c from=translated src=- shape=b14ee516 vocab=5caaab6c
-/
@[simp]
theorem twoCutoff_apply (R : ℕ) : twoCutoff R = 2 := rfl

/--
@isnad1 id=eq.0h0v.s4.3ca9ed943e05 from=translated src=- shape=bcda7985 vocab=8f9ca5a2
-/
theorem primesLE_two : Nat.primesLE 2 = {2} := by
  decide

/--
@isnad1 id=eq.0h0v.s3.66e2cdc2b7b3 from=translated src=- shape=3c26ae4f vocab=35f16702
-/
@[simp]
theorem primeProduct_two : primeProduct 2 = 2 := by
  simp [primeProduct, primesLE_two]

/--
@isnad1 id=eq.1h1v.s5.99d4bc3f674b from=translated src=- shape=29e62634 vocab=17709502
-/
theorem localDensity_two_of_even {m : ℕ} (hm : Even m) :
    localDensity m 2 = (1 : ℝ) / 2 := by
  rw [localDensity, shiftedBadResidueCount_prime Nat.prime_two,
    ite_eq_left (even_iff_two_dvd.mp hm)]
  norm_num

/--
@isnad1 id=eq.1h1v.s5.c5a3233fbb76 from=translated src=- shape=29e62634 vocab=02039eaf
-/
@[simp]
theorem localSieveProduct_two_of_even {m : ℕ} (hm : Even m) :
    localSieveProduct m 2 = (1 : ℝ) / 2 := by
  simp [localSieveProduct, primesLE_two, localDensity_two_of_even hm]
  norm_num

/--
@isnad1 id=eq.1h2v.s4.1856f7fbbbdc from=translated src=- shape=f4387a6b vocab=9a7ee8f4
-/
@[simp]
theorem twoSelberg_prodPrimes (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 2 hm).prodPrimes = 2 := by
  rfl

/--
@isnad1 id=eq.1h2v.s4.6dd83f29e96f from=translated src=- shape=33942627 vocab=5d308fa9
-/
@[simp, nolint simpNF]
theorem twoSelberg_level (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 2 hm).level = 4 := by
  rw [minimizingSelbergSieve_level_of_one_le hm (by norm_num : 1 ≤ 2)]
  norm_num

/--
@isnad1 id=eq.1h2v.s5.4a0e28714426 from=translated src=- shape=bf0cc58b vocab=2eac0f55
-/
theorem twoSelberg_truncatedDivisors (m R : ℕ) (hm : Even m) :
    SelbergFundamental.truncatedDivisors
      (minimizingSelbergSieve m R 2 hm) = {1, 2} := by
  ext d
  rw [SelbergFundamental.mem_truncatedDivisors]
  simp only [twoSelberg_prodPrimes, twoSelberg_level, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hd, _⟩
    have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hdLe : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> simp_all
  · rintro (rfl | rfl) <;> norm_num

/--
@isnad1 id=eq.1h2v.s5.f748eafb42fd from=translated src=- shape=cb9e06b5 vocab=ffa38010
-/
@[simp]
theorem twoSelberg_nu_two (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 2 hm).nu 2 = (1 : ℝ) / 2 := by
  change sieveDensity m 2 = (1 : ℝ) / 2
  rw [sieveDensity_apply_prime Nat.prime_two]
  exact localDensity_two_of_even hm

/--
@isnad1 id=eq.1h2v.s5.9f8da5aa9c4d from=translated src=- shape=2283e56f vocab=c85581d6
-/
@[simp]
theorem twoSelberg_selbergTerms_two (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 2 hm).selbergTerms 2 = 1 := by
  rw [BoundingSieve.selbergTerms_apply]
  simp [twoSelberg_nu_two, Nat.primeFactors]
  norm_num

/--
@isnad1 id=eq.1h2v.s4.b63118d683cd from=translated src=- shape=33942627 vocab=58c0fea2
-/
@[simp]
theorem twoSelberg_truncatedMass (m R : ℕ) (hm : Even m) :
    SelbergFundamental.truncatedMass
      (minimizingSelbergSieve m R 2 hm) = 2 := by
  rw [SelbergFundamental.truncatedMass, twoSelberg_truncatedDivisors]
  simp
  norm_num

/--
@isnad1 id=truncate.0h0v.s3.5a2d51217286 from=translated src=- shape=aa0f4b0e vocab=05370b74
-/
theorem truncatedMassLocalProductUpperBound_twoCutoff :
    TruncatedMassLocalProductUpperBound twoCutoff 1 := by
  intro m R _hm hmEven _hR
  simp [twoSelberg_truncatedMass, localSieveProduct_two_of_even hmEven]

/--
@isnad1 id=eq.1h2v.s5.97c9a555de22 from=translated src=- shape=cc6ef2fa vocab=cb9dd896
-/
@[simp]
theorem twoSelberg_minimizingWeight_two (m R : ℕ) (hm : Even m) :
    SelbergFundamental.minimizingWeight
      (minimizingSelbergSieve m R 2 hm) 2 = -1 := by
  let s := minimizingSelbergSieve m R 2 hm
  have hcoord := SelbergFundamental.diagonalCoordinate_minimizingWeight
    s (l := 2) (by
      change 2 ∣ primeProduct 2
      simp)
  change (∑ d ∈ s.prodPrimes.divisors,
      if 2 ∣ d then s.nu d * SelbergFundamental.minimizingWeight s d else 0) =
        SelbergFundamental.minimizingDiagonal s 2 at hcoord
  have hdiv : s.prodPrimes.divisors = {1, 2} := by
    change (primeProduct 2).divisors = {1, 2}
    rw [primeProduct_two]
    decide
  rw [hdiv] at hcoord
  norm_num at hcoord
  rw [show s.nu 2 = (1 / 2 : ℝ) by
    exact twoSelberg_nu_two m R hm] at hcoord
  have hmem : 2 ∈ SelbergFundamental.truncatedDivisors s := by
    change 2 ∈ SelbergFundamental.truncatedDivisors
      (minimizingSelbergSieve m R 2 hm)
    rw [twoSelberg_truncatedDivisors]
    simp
  rw [SelbergFundamental.minimizingDiagonal, ite_eq_left hmem] at hcoord
  change (1 / 2 : ℝ) * SelbergFundamental.minimizingWeight s 2 =
    (μ 2 : ℝ) * s.selbergTerms 2 /
      SelbergFundamental.truncatedMass s at hcoord
  rw [show (μ 2 : ℝ) = -1 by
      exact_mod_cast ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    show s.selbergTerms 2 = 1 by exact twoSelberg_selbergTerms_two m R hm,
    show SelbergFundamental.truncatedMass s = 2 by
      exact twoSelberg_truncatedMass m R hm] at hcoord
  linarith

/--
@isnad1 id=eq.1h2v.s5.2b608d90db12 from=translated src=- shape=456d5a5e vocab=777f7810
-/
@[simp]
theorem twoSelberg_lambdaSquared_one (m R : ℕ) (hm : Even m) :
    BoundingSieve.lambdaSquared
      (SelbergFundamental.minimizingWeight
        (minimizingSelbergSieve m R 2 hm)) 1 = 1 := by
  simp [BoundingSieve.lambdaSquared, SelbergFundamental.minimizingWeight_one]

/--
@isnad1 id=eq.1h2v.s5.c57a28949817 from=translated src=- shape=7a849464 vocab=0d3f4f66
-/
@[simp]
theorem twoSelberg_lambdaSquared_two (m R : ℕ) (hm : Even m) :
    BoundingSieve.lambdaSquared
      (SelbergFundamental.minimizingWeight
        (minimizingSelbergSieve m R 2 hm)) 2 = -1 := by
  unfold BoundingSieve.lambdaSquared
  rw [show (2 : ℕ).divisors = {1, 2} by decide]
  norm_num [SelbergFundamental.minimizingWeight_one,
    twoSelberg_minimizingWeight_two]

/--
@isnad1 id=eq.1h2v.s4.376ebae77037 from=translated src=- shape=e3f50372 vocab=14a24aa3
-/
@[simp]
theorem twoSelberg_remainderMajorant (m R : ℕ) (hm : Even m) :
    minimizingWeightRemainderMajorant m R 2 hm = 3 := by
  unfold minimizingWeightRemainderMajorant
  change (∑ d ∈ (minimizingSelbergSieve m R 2 hm).prodPrimes.divisors,
      if (d : ℝ) ≤ (minimizingSelbergSieve m R 2 hm).level then
        |BoundingSieve.lambdaSquared
            (SelbergFundamental.minimizingWeight
              (minimizingSelbergSieve m R 2 hm)) d| *
          ((2 ^ d.primeFactors.card : ℕ) : ℝ)
      else 0) = 3
  rw [show (minimizingSelbergSieve m R 2 hm).prodPrimes.divisors = {1, 2} by
    change (primeProduct 2).divisors = {1, 2}
    rw [primeProduct_two]
    decide]
  have hprimeFactors : (2 : ℕ).primeFactors = {2} := by
    simpa using Nat.primeFactors_prime_pow (p := 2) (k := 1) (by norm_num) Nat.prime_two
  simp [twoSelberg_lambdaSquared_one, twoSelberg_lambdaSquared_two, hprimeFactors]
  norm_num

/--
@isnad1 id=combinat.0h0v.s3.a00aed42f71e from=translated src=- shape=aa0f4b0e vocab=ab77b17b
-/
theorem combinatorialRemainderLocalProductUpperBound_twoCutoff :
    CombinatorialRemainderLocalProductUpperBound twoCutoff 2 := by
  intro m R _hm hmEven hR
  rw [twoCutoff_apply, twoSelberg_remainderMajorant,
    localSieveProduct_two_of_even hmEven]
  have hR' : (3 : ℝ) ≤ R := by exact_mod_cast hR
  norm_num
  nlinarith

/--
@isnad1 id=eq.1h2v.s5.2f518d1f42eb from=translated src=- shape=456d5a5e vocab=304340b1
-/
theorem twoSelberg_rem_one (m R : ℕ) (hm : Even m) :
    (minimizingSelbergSieve m R 2 hm).rem 1 = 0 := by
  change (boundingSieve m R 2 hm).rem 1 = 0
  rw [boundingSieve_rem_eq_excess_sub_fraction hm (by norm_num)
    (by simp : Squarefree 1)]
  have hmod : R % 1 = 0 := Nat.mod_one R
  simp [residueExcessCount, hmod]

/-! ## A natural bounded identity cutoff `min R 2` is the largest initial prime cutoff whose entire divisor lattice can be evaluated here without any asymptotic input. -/

/-- Natural cutoff retaining only the parity prime in the finite terminal model.-/
def parityCutoff (R : ℕ) : ℕ := min R 2

/--
@isnad1 id=eq.1h1v.s4.42623e645c4c from=translated src=- shape=97c35add vocab=8b610f16
-/
theorem parityCutoff_eq_two {R : ℕ} (hR : 3 ≤ R) : parityCutoff R = 2 := by
  simp [parityCutoff, Nat.min_eq_right (by omega : 2 ≤ R)]

/--
@isnad1 id=truncate.0h0v.s3.02013a27513f from=translated src=- shape=aa0f4b0e vocab=615e3d95
-/
theorem truncatedMassLocalProductUpperBound_parityCutoff :
    TruncatedMassLocalProductUpperBound parityCutoff 1 := by
  intro m R hm hmEven hR
  simpa [parityCutoff_eq_two hR] using
    truncatedMassLocalProductUpperBound_twoCutoff m R hm hmEven hR

/--
@isnad1 id=combinat.0h0v.s3.de82217af138 from=translated src=- shape=aa0f4b0e vocab=bbe869ab
-/
theorem combinatorialRemainderLocalProductUpperBound_parityCutoff :
    CombinatorialRemainderLocalProductUpperBound parityCutoff 2 := by
  intro m R hm hmEven hR
  simpa [parityCutoff_eq_two hR] using
    combinatorialRemainderLocalProductUpperBound_twoCutoff m R hm hmEven hR

end BFPSTwoAffine

end

end RankAmplification
