import Tengoku.Rankamplificationtotient.RankAmplification.ReciprocalBrunTitchmarsh
import Tengoku.Rankamplificationtotient.RankAmplification.SelbergFundamentalLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A Selberg terminal reduction for dyadic Brun--Titchmarsh This file constructs the one-dimensional Selberg sieve for a finite arithmetic progression and reduces `DyadicBrunTitchmarshHypothesis` to two explicit finite estimates for the canonical minimizing weights. -/

namespace RankAmplification

open Finset Nat ArithmeticFunction
open scoped BigOperators Nat.Prime ArithmeticFunction.Moebius

noncomputable section

namespace BrunTitchmarsh

/-! ## A primitive arithmetic progression -/

/-- A positive-step arithmetic progression whose step and initial value are coprime.-/
structure Progression where
  /-- Positive common difference of the progression.-/
  step : ℕ
  /-- Initial value of the progression.-/
  base : ℕ
  step_pos : 0 < step
  coprime : step.Coprime base

namespace Progression

variable (P : Progression)

/-- Value of the progression at parameter `t`.-/
def value (t : ℕ) : ℕ := P.base + P.step * t

theorem value_strictMono : StrictMono P.value := by
  intro t u htu
  unfold value
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left htu P.step_pos) P.base

/-- Embedding of progression parameters into their values.-/
def valueEmbedding : ℕ ↪ ℕ where
  toFun := P.value
  inj' := P.value_strictMono.injective

/-- First `R` values of the progression, used as sieve support.-/
def support (R : ℕ) : Finset ℕ :=
  (Finset.range R).map P.valueEmbedding

@[simp]
theorem mem_support {R n : ℕ} :
    n ∈ P.support R ↔ ∃ t < R, P.value t = n := by
  simp [support, valueEmbedding]

/-- Parameter residues on which the progression value is divisible by `d`.-/
def badResidueSet (d : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun t ↦ d ∣ P.value t

@[simp]
theorem mem_badResidueSet {d : ℕ} {t : Fin d} :
    t ∈ P.badResidueSet d ↔ d ∣ P.value t := by
  simp [badResidueSet]

/-- Number of progression parameters modulo `d` producing a divisible value.-/
def badResidueCount (d : ℕ) : ℕ := (P.badResidueSet d).card

theorem value_modEq {d t u : ℕ} (htu : t ≡ u [MOD d]) :
    P.value t ≡ P.value u [MOD d] := by
  unfold value
  exact htu.mul_left P.step |>.add_left P.base

/-- Multiplication by the step is cancellable modulo every modulus coprime to it.-/
theorem badResidueSet_card_le_one {d : ℕ} (hcop : P.step.Coprime d) :
    (P.badResidueSet d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hxDiv := P.mem_badResidueSet.mp hx
  have hyDiv := P.mem_badResidueSet.mp hy
  have hxZero : (P.base : ZMod d) + P.step * x.val = 0 := by
    have hzero : ((P.value x : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff (P.value x) d).mpr hxDiv
    simpa [value] using hzero
  have hyZero : (P.base : ZMod d) + P.step * y.val = 0 := by
    have hzero : ((P.value y : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff (P.value y) d).mpr hyDiv
    simpa [value] using hzero
  have hstepUnit : IsUnit (P.step : ZMod d) :=
    (ZMod.isUnit_iff_coprime P.step d).mpr hcop
  have hxy : (x.val : ZMod d) = y.val := by
    rw [← hstepUnit.mul_left_inj]
    linear_combination hxZero - hyZero
  apply Fin.ext
  have hmod : x.val ≡ y.val [MOD d] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hxy
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt x.isLt,
    Nat.mod_eq_of_lt y.isLt] using hmod

/-- A primitive linear congruence has a root modulo every positive modulus coprime to its step.-/
theorem badResidueSet_nonempty {d : ℕ} (hd : 0 < d)
    (hcop : P.step.Coprime d) : (P.badResidueSet d).Nonempty := by
  letI : NeZero d := ⟨hd.ne'⟩
  have hstepUnit : IsUnit (P.step : ZMod d) :=
    (ZMod.isUnit_iff_coprime P.step d).mpr hcop
  let root : ZMod d := -(P.step : ZMod d)⁻¹ * P.base
  let t : Fin d := (ZMod.finEquiv d).symm root
  refine ⟨t, P.mem_badResidueSet.mpr ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have ht : (t.val : ZMod d) = root := by
    have hfin : (ZMod.finEquiv d) t = (t.val : ZMod d) := by
      cases d with
      | zero => exact Fin.elim0 t
      | succ d =>
          change t = (t.val : ZMod (d + 1))
          exact (ZMod.natCast_zmod_val (n := d + 1) t).symm
    calc
      (t.val : ZMod d) = (ZMod.finEquiv d) t := hfin.symm
      _ = root := (ZMod.finEquiv d).apply_symm_apply root
  rw [show ((P.value t : ℕ) : ZMod d) =
      (P.base : ZMod d) + P.step * t.val by simp [value]]
  rw [ht]
  simp only [root]
  calc
    (P.base : ZMod d) + P.step * (-(P.step : ZMod d)⁻¹ * P.base) =
        P.base - ((P.step : ZMod d) * (P.step : ZMod d)⁻¹) * P.base := by ring
    _ = 0 := by rw [ZMod.mul_inv_of_unit _ hstepUnit]; ring

theorem badResidueCount_eq_one {d : ℕ} (hd : 0 < d)
    (hcop : P.step.Coprime d) : P.badResidueCount d = 1 := by
  apply Nat.le_antisymm
  · exact P.badResidueSet_card_le_one hcop
  · exact (P.badResidueSet_nonempty hd hcop).card_pos

/-! ## Exact incomplete-block counts -/

/-- Parameters below `R` whose progression value is divisible by `d`.-/
def divisibleParameterSet (R d : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ d ∣ P.value t

@[simp]
theorem mem_divisibleParameterSet {R d t : ℕ} :
    t ∈ P.divisibleParameterSet R d ↔ t < R ∧ d ∣ P.value t := by
  simp [divisibleParameterSet]

/-- Parameters below `R` in the residue class `a` modulo `d`.-/
def parameterResidueFiber (_P : Progression) (R d : ℕ) (a : Fin d) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ t ≡ a.val [MOD d]

@[simp]
theorem mem_parameterResidueFiber {R d : ℕ} {a : Fin d} {t : ℕ} :
    t ∈ P.parameterResidueFiber R d a ↔ t < R ∧ t ≡ a.val [MOD d] := by
  simp [parameterResidueFiber]

theorem card_parameterResidueFiber {R d : ℕ} (hd : 0 < d) (a : Fin d) :
    (P.parameterResidueFiber R d a).card =
      R / d + if a.val < R % d then 1 else 0 := by
  rw [parameterResidueFiber, ← Nat.count_eq_card_filter_range]
  simpa only [Nat.mod_eq_of_lt a.isLt] using Nat.count_modEq_card R hd a.val

/-- Bad residue classes represented once beyond the complete quotient blocks.-/
def residueExcessCount (R d : ℕ) : ℕ :=
  ((P.badResidueSet d).filter fun a ↦ a.val < R % d).card

theorem residueExcessCount_le_one {R d : ℕ} (hcop : P.step.Coprime d) :
    P.residueExcessCount R d ≤ 1 := by
  exact (Finset.card_filter_le _ _).trans (P.badResidueSet_card_le_one hcop)

theorem divisibleParameterSet_eq_biUnion {R d : ℕ} (hd : 0 < d) :
    P.divisibleParameterSet R d =
      (P.badResidueSet d).biUnion (P.parameterResidueFiber R d) := by
  ext t
  rw [mem_divisibleParameterSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨htR, htDiv⟩
    let a : Fin d := ⟨t % d, Nat.mod_lt t hd⟩
    have hta : t ≡ a.val [MOD d] := (Nat.mod_modEq t d).symm
    have hvalue := P.value_modEq hta
    have haDiv : d ∣ P.value a.val :=
      Nat.modEq_zero_iff_dvd.mp (hvalue.symm.trans htDiv.modEq_zero_nat)
    exact ⟨a, P.mem_badResidueSet.mpr haDiv,
      P.mem_parameterResidueFiber.mpr ⟨htR, hta⟩⟩
  · rintro ⟨a, haRoot, hta⟩
    have htaData := P.mem_parameterResidueFiber.mp hta
    have haDiv : d ∣ P.value a := P.mem_badResidueSet.mp haRoot
    have hvalue := P.value_modEq htaData.2
    exact ⟨htaData.1,
      Nat.modEq_zero_iff_dvd.mp (hvalue.trans haDiv.modEq_zero_nat)⟩

theorem parameterResidueFiber_pairwiseDisjoint (R d : ℕ) :
    ((P.badResidueSet d : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint
      (P.parameterResidueFiber R d) := by
  intro a _ha b _hb hab
  change Disjoint (P.parameterResidueFiber R d a)
    (P.parameterResidueFiber R d b)
  rw [Finset.disjoint_left]
  intro t hta htb
  have hat := (P.mem_parameterResidueFiber.mp hta).2
  have hbt := (P.mem_parameterResidueFiber.mp htb).2
  apply hab
  apply Fin.ext
  have habMod : a.val ≡ b.val [MOD d] := hat.symm.trans hbt
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt,
    Nat.mod_eq_of_lt b.isLt] using habMod

theorem card_divisibleParameterSet_eq {R d : ℕ} (hd : 0 < d)
    (hcop : P.step.Coprime d) :
    (P.divisibleParameterSet R d).card =
      R / d + P.residueExcessCount R d := by
  rw [P.divisibleParameterSet_eq_biUnion hd,
    Finset.card_biUnion (P.parameterResidueFiber_pairwiseDisjoint R d)]
  simp_rw [P.card_parameterResidueFiber hd]
  rw [Finset.sum_add_distrib]
  have hcard : (P.badResidueSet d).card = 1 :=
    P.badResidueCount_eq_one hd hcop
  have hsum : (∑ x ∈ P.badResidueSet d,
      if x.val < R % d then 1 else 0) = P.residueExcessCount R d := by
    rw [residueExcessCount, Finset.card_filter]
  simp only [Finset.sum_const_nat]
  rw [hcard, hsum, one_mul]

/-! ## The one-dimensional sieve datum -/

/-- Sieve primes through `z` that do not divide the progression step.-/
def activePrimeSet (z : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter fun p ↦ ¬p ∣ P.step

@[simp]
theorem mem_activePrimeSet {z p : ℕ} :
    p ∈ P.activePrimeSet z ↔ p.Prime ∧ p ≤ z ∧ ¬p ∣ P.step := by
  simp only [activePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  aesop

/-- Product of all active sieve primes through `z`.-/
def activePrimeProduct (z : ℕ) : ℕ :=
  ∏ p ∈ P.activePrimeSet z, p

theorem activePrimeProduct_squarefree (z : ℕ) :
    Squarefree (P.activePrimeProduct z) := by
  rw [activePrimeProduct]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq ↦ ?_)
    (fun p hp ↦ (P.mem_activePrimeSet.mp hp).1.squarefree)
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (P.mem_activePrimeSet.mp hp).1
    (P.mem_activePrimeSet.mp hq).1).mpr hpq

theorem step_coprime_activePrimeProduct (z : ℕ) :
    P.step.Coprime (P.activePrimeProduct z) := by
  rw [activePrimeProduct, Nat.coprime_prod_right_iff]
  intro p hp
  have hpData := P.mem_activePrimeSet.mp hp
  exact (hpData.1.coprime_iff_not_dvd.mpr hpData.2.2).symm

theorem step_coprime_of_dvd_activePrimeProduct {z d : ℕ}
    (hd : d ∣ P.activePrimeProduct z) : P.step.Coprime d :=
  (P.step_coprime_activePrimeProduct z).coprime_dvd_right hd

/-- Local density of the unique forbidden residue class modulo an active prime.-/
def localDensity (_P : Progression) (p : ℕ) : ℝ := (p : ℝ)⁻¹

/-- Multiplicative sieve density generated from the prime local densities.-/
def sieveDensity : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors P.localDensity

theorem sieveDensity_isMultiplicative : P.sieveDensity.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors P.localDensity

@[simp]
theorem sieveDensity_apply_prime {p : ℕ} (hp : p.Prime) :
    P.sieveDensity p = (p : ℝ)⁻¹ := by
  rw [sieveDensity, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp.primeFactors, localDensity]

theorem sieveDensity_eq_inv {d : ℕ} (hd : d ≠ 0) (hsq : Squarefree d) :
    P.sieveDensity d = (d : ℝ)⁻¹ := by
  rw [sieveDensity, ArithmeticFunction.prodPrimeFactors_apply hd]
  simp only [localDensity]
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq]

/-- Mathlib's finite bounding sieve for a primitive progression.-/
def boundingSieve (R z : ℕ) : BoundingSieve where
  support := P.support R
  prodPrimes := P.activePrimeProduct z
  prodPrimes_squarefree := P.activePrimeProduct_squarefree z
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ by norm_num
  totalMass := R
  nu := P.sieveDensity
  nu_mult := P.sieveDensity_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpd
    rw [P.sieveDensity_apply_prime hp]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpd
    rw [P.sieveDensity_apply_prime hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- Selberg-sieve structure for the finite progression support.-/
def selbergSieve (R z : ℕ) (level : ℝ) (hlevel : 1 ≤ level) : SelbergSieve where
  toBoundingSieve := P.boundingSieve R z
  level := level
  one_le_level := hlevel

theorem boundingSieve_multSum (R z d : ℕ) :
    (P.boundingSieve R z).multSum d = (P.divisibleParameterSet R d).card := by
  simp [BoundingSieve.multSum, boundingSieve, support, valueEmbedding,
    divisibleParameterSet]
  rw [Finset.filter_map, Finset.card_map]
  rfl

theorem boundingSieve_rem {R z d : ℕ} :
    (P.boundingSieve R z).rem d =
      (P.divisibleParameterSet R d).card - P.sieveDensity d * R := by
  rw [BoundingSieve.rem, P.boundingSieve_multSum]
  rfl

theorem boundingSieve_rem_eq_excess_sub_fraction
    {R z d : ℕ} (hdDvd : d ∣ P.activePrimeProduct z) :
    (P.boundingSieve R z).rem d =
      (P.residueExcessCount R d : ℝ) - (R % d : ℕ) / d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (P.boundingSieve R z).prodPrimes_ne_zero hdDvd)
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hdDvd (P.activePrimeProduct_squarefree z)
  rw [P.boundingSieve_rem, P.card_divisibleParameterSet_eq hd0
    (P.step_coprime_of_dvd_activePrimeProduct hdDvd), P.sieveDensity_eq_inv hd0.ne' hsq]
  norm_num only [Nat.cast_add]
  have hR : (R : ℝ) = (d : ℝ) * (R / d : ℕ) + (R % d : ℕ) := by
    exact_mod_cast (Nat.mod_add_div R d).symm.trans (by omega)
  rw [hR]
  have hdCast : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp
  ring

theorem abs_boundingSieve_rem_le_one {R z d : ℕ}
    (hdDvd : d ∣ P.activePrimeProduct z) :
    |(P.boundingSieve R z).rem d| ≤ 1 := by
  rw [P.boundingSieve_rem_eq_excess_sub_fraction hdDvd]
  have hd0 : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (P.boundingSieve R z).prodPrimes_ne_zero hdDvd)
  have hcop := P.step_coprime_of_dvd_activePrimeProduct hdDvd
  have hexcess : (P.residueExcessCount R d : ℝ) ≤ 1 := by
    exact_mod_cast P.residueExcessCount_le_one hcop
  have hfrac : (((R % d : ℕ) : ℝ) / d) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hd0)]
    exact_mod_cast (Nat.mod_lt R hd0).le
  have hexcess0 : (0 : ℝ) ≤ P.residueExcessCount R d := by positivity
  have hfrac0 : (0 : ℝ) ≤ ((R % d : ℕ) : ℝ) / d := by positivity
  rw [abs_le]
  constructor <;> linarith

/-! ## Sifted parameters and the exact minimizing-weight endpoint -/

/-- Parameters surviving every active-prime divisibility test through `z`.-/
def siftedParameterSet (R z : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦
    Nat.Coprime (P.activePrimeProduct z) (P.value t)

@[simp]
theorem mem_siftedParameterSet {R z t : ℕ} :
    t ∈ P.siftedParameterSet R z ↔
      t < R ∧ Nat.Coprime (P.activePrimeProduct z) (P.value t) := by
  simp [siftedParameterSet]

/-- Parameters below `R` whose progression value is prime.-/
def primeParameterSet (R : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ (P.value t).Prime

@[simp]
theorem mem_primeParameterSet {R t : ℕ} :
    t ∈ P.primeParameterSet R ↔ t < R ∧ (P.value t).Prime := by
  simp [primeParameterSet]

theorem primeParameterSet_subset_siftedParameterSet {R z : ℕ}
    (hlarge : ∀ t < R, z < P.value t) :
    P.primeParameterSet R ⊆ P.siftedParameterSet R z := by
  intro t ht
  have htData := P.mem_primeParameterSet.mp ht
  apply P.mem_siftedParameterSet.mpr
  refine ⟨htData.1, ?_⟩
  rw [Progression.activePrimeProduct, Nat.coprime_prod_left_iff]
  intro p hpMem
  have hpData := P.mem_activePrimeSet.mp hpMem
  exact hpData.1.coprime_iff_not_dvd.mpr fun hpDiv ↦ by
    have hpEq : p = P.value t :=
      (Nat.prime_dvd_prime_iff_eq hpData.1 htData.2).mp hpDiv
    have hzlt : z < p := by simpa [hpEq] using hlarge t htData.1
    exact (not_lt_of_ge hpData.2.1) hzlt

/-- The canonical finite minimizer at Λ² level `(max 1 z)²`.-/
def minimizingSieve (R z : ℕ) : SelbergSieve :=
  P.selbergSieve R z (((max 1 z : ℕ) : ℝ) ^ 2) (by
    have h : (1 : ℝ) ≤ (max 1 z : ℕ) := by
      exact_mod_cast Nat.le_max_left 1 z
    nlinarith)

@[simp]
theorem minimizingSieve_totalMass (R z : ℕ) :
    (P.minimizingSieve R z).totalMass = R := rfl

/-- Euler product of local progression survival densities through `z`.-/
def localSieveProduct (z : ℕ) : ℝ :=
  ∏ p ∈ P.activePrimeSet z, (1 - (p : ℝ)⁻¹)

theorem localSieveProduct_pos (z : ℕ) : 0 < P.localSieveProduct z := by
  unfold localSieveProduct
  exact Finset.prod_pos fun p hp ↦
    BFPSTwoAffine.directMertensFactor_pos (P.mem_activePrimeSet.mp hp).1

/-- The explicit absolute remainder carrier after `|r_d| ≤ 1`.-/
def minimizingWeightRemainderMajorant (R z : ℕ) : ℝ :=
  let s := P.minimizingSieve R z
  ∑ d ∈ s.prodPrimes.divisors,
    if (d : ℝ) ≤ s.level then
      |BoundingSieve.lambdaSquared (SelbergFundamental.minimizingWeight s) d|
    else 0

theorem levelRestrictedRemainder_le_majorant (R z : ℕ) :
    SelbergFundamental.levelRestrictedRemainder (P.minimizingSieve R z) ≤
      P.minimizingWeightRemainderMajorant R z := by
  let s := P.minimizingSieve R z
  change SelbergFundamental.levelRestrictedRemainder s ≤
    P.minimizingWeightRemainderMajorant R z
  unfold SelbergFundamental.levelRestrictedRemainder
  change (∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ) ≤ s.level then
        |BoundingSieve.lambdaSquared (SelbergFundamental.minimizingWeight s) d| *
          |s.rem d|
      else 0) ≤
    ∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ) ≤ s.level then
        |BoundingSieve.lambdaSquared (SelbergFundamental.minimizingWeight s) d|
      else 0
  apply Finset.sum_le_sum
  intro d hdMem
  by_cases hlevel : (d : ℝ) ≤ s.level
  · rw [ite_eq_left hlevel, ite_eq_left hlevel]
    have hdDvd : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hdMem
    have hrem : |s.rem d| ≤ 1 := by
      exact P.abs_boundingSieve_rem_le_one hdDvd
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hrem (abs_nonneg _)
  · rw [ite_eq_right hlevel, ite_eq_right hlevel]

end Progression

/-! ## The two genuinely terminal finite estimates -/

/-- Terminal lower bound for the truncated Selberg mass, expressed via the local product.-/
def TruncatedMassLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ P : Progression, ∀ R, 3 ≤ R →
    (SelbergFundamental.truncatedMass
      (P.minimizingSieve R (cutoff R)))⁻¹ ≤
        C * P.localSieveProduct (cutoff R)

/-- Terminal upper bound for the combinatorial remainder in local-product scale.-/
def CombinatorialRemainderLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ P : Progression, ∀ R, 3 ≤ R →
    P.minimizingWeightRemainderMajorant R (cutoff R) ≤
      C * R * P.localSieveProduct (cutoff R)

/-- Packaged Selberg upper bound for a finite arithmetic progression.-/
def ProgressionSelbergUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ P : Progression, ∀ R, 3 ≤ R →
    (P.boundingSieve R (cutoff R)).siftedSum ≤
      C * R * P.localSieveProduct (cutoff R)

theorem progressionSelbergUpperBound_of_mass_and_remainder
    {cutoff : ℕ → ℕ} {Cmass Crem : ℝ}
    (hmass : TruncatedMassLocalProductUpperBound cutoff Cmass)
    (hrem : CombinatorialRemainderLocalProductUpperBound cutoff Crem) :
    ProgressionSelbergUpperBound cutoff (Cmass + Crem) := by
  intro P R hR
  let s := P.minimizingSieve R (cutoff R)
  have hfinite := SelbergFundamental.siftedSum_le_minimizing_main_add_error s
  have herrEq :=
    SelbergFundamental.errSum_lambdaSquared_minimizingWeight_eq_levelRestrictedRemainder s
  have hlevel := P.levelRestrictedRemainder_le_majorant R (cutoff R)
  have hmass' := hmass P R hR
  have hrem' := hrem P R hR
  have hsMass : s.totalMass = (R : ℝ) := rfl
  change s.siftedSum ≤
    (Cmass + Crem) * R * P.localSieveProduct (cutoff R)
  calc
    s.siftedSum ≤ (R : ℝ) *
        (SelbergFundamental.truncatedMass s)⁻¹ +
        s.errSum (BoundingSieve.lambdaSquared
          (SelbergFundamental.minimizingWeight s)) := by
      rw [hsMass] at hfinite
      exact hfinite
    _ = (R : ℝ) * (SelbergFundamental.truncatedMass s)⁻¹ +
        SelbergFundamental.levelRestrictedRemainder s := by rw [herrEq]
    _ ≤ (R : ℝ) * (Cmass * P.localSieveProduct (cutoff R)) +
        Crem * R * P.localSieveProduct (cutoff R) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmass' (by positivity))
        (hlevel.trans hrem')
    _ = (Cmass + Crem) * R * P.localSieveProduct (cutoff R) := by ring

/-! ## Unconditional local-product comparison -/

theorem localSieveProduct_eq_directMertens_mul_correction
    (P : Progression) (z : ℕ) :
    P.localSieveProduct z =
      BFPSTwoAffine.directMertensProduct z *
        ∏ p ∈ Nat.primesLE z,
          BFPSTwoAffine.multiplierCorrectionFactor P.step p := by
  unfold Progression.localSieveProduct Progression.activePrimeSet
    BFPSTwoAffine.directMertensProduct
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primesLE hp
  by_cases hpd : p ∣ P.step
  · simp only [hpd, not_true_eq_false, ite_false,
      BFPSTwoAffine.multiplierCorrectionFactor, ite_true]
    field_simp [(BFPSTwoAffine.directMertensFactor_pos hpPrime).ne']
  · simp [hpd, BFPSTwoAffine.multiplierCorrectionFactor]

theorem localSieveProduct_le_directMertens_mul_totientWeight
    (P : Progression) (z : ℕ) :
    P.localSieveProduct z ≤
      BFPSTwoAffine.directMertensProduct z * totientWeight P.step := by
  rw [localSieveProduct_eq_directMertens_mul_correction]
  rw [totientWeight_eq_eulerWeight P.step_pos.ne']
  exact mul_le_mul_of_nonneg_left
    (BFPSTwoAffine.correctionProduct_le_totientEulerWeight P.step_pos.ne')
    (BFPSTwoAffine.directMertensProduct_pos z).le

theorem localSieveProduct_le_directMertens_mul_totient_ratio
    (P : Progression) (z : ℕ) :
    P.localSieveProduct z ≤
      BFPSTwoAffine.directMertensProduct z *
        ((P.step : ℝ) / (P.step.totient : ℝ)) := by
  simpa [totientWeight] using
    localSieveProduct_le_directMertens_mul_totientWeight P z

/-! ## Exact parametrization of a dyadic residue interval -/

/-- Length of the `j`th dyadic parameter interval.-/
def dyadicLength (j : ℕ) : ℕ := 2 ^ j

/-- Canonical representative of `a` modulo `D`.-/
def reducedResidue (D a : ℕ) : ℕ := a % D

/-- Starting quotient index of the dyadic residue interval.-/
def dyadicStartIndex (D a j : ℕ) : ℕ :=
  dyadicLength j + if reducedResidue D a = 0 then 1 else 0

/-- First progression value representing the dyadic residue interval.-/
def dyadicBase (D a j : ℕ) : ℕ :=
  reducedResidue D a + D * dyadicStartIndex D a j

/-- Progression parametrizing one dyadic interval in the residue class `a mod D`.-/
def dyadicProgression (D a j : ℕ) (hD : 0 < D) (hcop : D.Coprime a) :
    Progression where
  step := D
  base := dyadicBase D a j
  step_pos := hD
  coprime := by
    have hb : D.Coprime (reducedResidue D a) := by
      apply (Nat.coprime_add_mul_left_right D (reducedResidue D a) (a / D)).mp
      simpa [reducedResidue, Nat.mod_add_div] using hcop
    exact (Nat.coprime_add_mul_left_right D (reducedResidue D a)
      (dyadicStartIndex D a j)).mpr hb

@[simp]
theorem dyadicProgression_step {D a j : ℕ} {hD : 0 < D} {hcop : D.Coprime a} :
    (dyadicProgression D a j hD hcop).step = D := rfl

@[simp]
theorem dyadicProgression_base {D a j : ℕ} {hD : 0 < D} {hcop : D.Coprime a} :
    (dyadicProgression D a j hD hcop).base = dyadicBase D a j := rfl

theorem residuePrimeIntervalSet_reducedResidue (D a L U : ℕ) :
    residuePrimeIntervalSet D a L U =
      residuePrimeIntervalSet D (reducedResidue D a) L U := by
  ext q
  simp only [mem_residuePrimeIntervalSet]
  have hmod : a % D ≡ a [MOD D] := Nat.mod_modEq a D
  constructor
  · rintro ⟨hL, hU, hp, hqa⟩
    exact ⟨hL, hU, hp, hqa.trans hmod.symm⟩
  · rintro ⟨hL, hU, hp, hqb⟩
    exact ⟨hL, hU, hp, hqb.trans hmod⟩

private theorem dyadic_parameter_data
    {D a j q : ℕ} (hD : 0 < D) (hcop : D.Coprime a)
    (hq : q ∈ residuePrimeIntervalSet D a
      (dyadicLength j * D) (2 * dyadicLength j * D)) :
    ∃ t < dyadicLength j,
      (dyadicProgression D a j hD hcop).value t = q := by
  let N := dyadicLength j
  let b := reducedResidue D a
  let k := q / D
  let K := dyadicStartIndex D a j
  have hqData := mem_residuePrimeIntervalSet.mp hq
  change N * D < q ∧ q ≤ 2 * N * D ∧ q.Prime ∧ q ≡ a [MOD D] at hqData
  have hbLt : b < D := by
    exact Nat.mod_lt a hD
  have hmod : q % D = b := hqData.2.2.2
  have hqEq : q = b + D * k := by
    calc
      q = q % D + D * (q / D) := (Nat.mod_add_div q D).symm
      _ = b + D * k := by rw [hmod]
  have hkLower : N ≤ k := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa only [mul_comm] using hqData.1.le
  have hkUpper : k ≤ 2 * N := by
    apply Nat.div_le_of_le_mul
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hqData.2.1
  by_cases hbZero : b = 0
  · have hkLower' : N + 1 ≤ k := by
      have hne : k ≠ N := by
        intro hk
        have hqEndpoint : q = N * D := by
          calc
            q = b + D * k := hqEq
            _ = N * D := by rw [hbZero, hk]; ring
        omega
      omega
    let t := k - (N + 1)
    have ht : t < N := by omega
    refine ⟨t, ht, ?_⟩
    have hK : K = N + 1 := by
      simp [K, dyadicStartIndex, N, b, hbZero]
    have hKt : K + t = k := by
      rw [hK]
      exact Nat.add_sub_of_le hkLower'
    change dyadicBase D a j + D * t = q
    change b + D * K + D * t = q
    calc
      b + D * K + D * t = b + D * (K + t) := by ring
      _ = b + D * k := by rw [hKt]
      _ = q := hqEq.symm
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hbZero
    have hkUpper' : k < 2 * N := by
      by_contra hnot
      have hk : k = 2 * N := by omega
      have hqForm : q = b + D * (2 * N) := by
        calc
          q = b + D * k := hqEq
          _ = b + D * (2 * N) := by rw [hk]
      have hstrict : 2 * N * D < q := by
        calc
          2 * N * D = D * (2 * N) := by ring
          _ < b + D * (2 * N) := by omega
          _ = q := hqForm.symm
      omega
    let t := k - N
    have ht : t < N := by omega
    refine ⟨t, ht, ?_⟩
    have hK : K = N := by
      simp [K, dyadicStartIndex, N, b, hbZero]
    have hKt : K + t = k := by
      rw [hK]
      exact Nat.add_sub_of_le hkLower
    change dyadicBase D a j + D * t = q
    change b + D * K + D * t = q
    calc
      b + D * K + D * t = b + D * (K + t) := by ring
      _ = b + D * k := by rw [hKt]
      _ = q := hqEq.symm

theorem residuePrimeIntervalCount_le_primeParameterSet
    {D a j : ℕ} (hD : 0 < D) (hcop : D.Coprime a) :
    residuePrimeIntervalCount D a (dyadicLength j * D)
        (2 * dyadicLength j * D) ≤
      ((dyadicProgression D a j hD hcop).primeParameterSet
        (dyadicLength j)).card := by
  unfold residuePrimeIntervalCount
  let P := dyadicProgression D a j hD hcop
  let source := residuePrimeIntervalSet D a
    (dyadicLength j * D) (2 * dyadicLength j * D)
  classical
  let parameter (q : ℕ) : ℕ :=
    if hq : q ∈ source then
      Classical.choose (dyadic_parameter_data hD hcop hq)
    else 0
  refine Finset.card_le_card_of_injOn parameter ?_ ?_
  · intro q hq
    have hqFin : q ∈ source := hq
    have hdata := Classical.choose_spec (dyadic_parameter_data hD hcop hqFin)
    have hparam : parameter q =
        Classical.choose (dyadic_parameter_data hD hcop hqFin) := by
      simp only [parameter]
      rw [dite_eq_left hqFin]
    apply P.mem_primeParameterSet.mpr
    rw [hparam]
    refine ⟨hdata.1, ?_⟩
    rw [hdata.2]
    exact (mem_residuePrimeIntervalSet.mp hqFin).2.2.1
  · intro q hq r hr heq
    have hqFin : q ∈ source := hq
    have hrFin : r ∈ source := hr
    have hqData := Classical.choose_spec (dyadic_parameter_data hD hcop hqFin)
    have hrData := Classical.choose_spec (dyadic_parameter_data hD hcop hrFin)
    have hqParam : parameter q =
        Classical.choose (dyadic_parameter_data hD hcop hqFin) := by
      simp only [parameter]
      rw [dite_eq_left hqFin]
    have hrParam : parameter r =
        Classical.choose (dyadic_parameter_data hD hcop hrFin) := by
      simp only [parameter]
      rw [dite_eq_left hrFin]
    calc
      q = P.value (parameter q) := by rw [hqParam]; exact hqData.2.symm
      _ = P.value (parameter r) := congrArg P.value heq
      _ = r := by rw [hrParam]; exact hrData.2

theorem residuePrimeIntervalSet_eq_empty_of_not_coprime
    {D a j : ℕ} (hD : 0 < D) (hcop : ¬D.Coprime a) :
    residuePrimeIntervalSet D a (dyadicLength j * D)
      (2 * dyadicLength j * D) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have hqData := mem_residuePrimeIntervalSet.mp hq
  let g := Nat.gcd D a
  have hgD : g ∣ D := Nat.gcd_dvd_left D a
  have hga : g ∣ a := Nat.gcd_dvd_right D a
  have hg1 : g ≠ 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one, g] using hcop
  have hgq : g ∣ q :=
    (hqData.2.2.2.dvd_iff hgD).mpr hga
  have hgEq : g = q := (Nat.dvd_prime hqData.2.2.1).mp hgq |>.resolve_left hg1
  have hgLe : g ≤ D := Nat.le_of_dvd hD hgD
  have hNPos : 0 < dyadicLength j := by
    exact pow_pos (by norm_num) j
  have hDle : D ≤ dyadicLength j * D := by
    rw [mul_comm]
    exact Nat.le_mul_of_pos_right D hNPos
  have hqLe : q ≤ D := hgEq ▸ hgLe
  omega

theorem residuePrimeIntervalCount_eq_zero_of_not_coprime
    {D a j : ℕ} (hD : 0 < D) (hcop : ¬D.Coprime a) :
    residuePrimeIntervalCount D a (dyadicLength j * D)
      (2 * dyadicLength j * D) = 0 := by
  rw [residuePrimeIntervalCount,
    residuePrimeIntervalSet_eq_empty_of_not_coprime hD hcop]
  simp

theorem dyadicProgression_value_gt_lower
    {D a j : ℕ} (hD : 0 < D) (hcop : D.Coprime a) (t : ℕ) :
    dyadicLength j * D < (dyadicProgression D a j hD hcop).value t := by
  by_cases hb : reducedResidue D a = 0
  · simp [Progression.value, dyadicProgression, dyadicBase,
      dyadicStartIndex, hb]
    nlinarith
  · have hbPos : 0 < reducedResidue D a := Nat.pos_of_ne_zero hb
    simp [Progression.value, dyadicProgression, dyadicBase,
      dyadicStartIndex, hb]
    nlinarith

/-- The exact elementary census: a dyadic interval contains at most `2^j` members of one residue class, including the non-coprime and zero-modulus cases.-/
theorem residuePrimeIntervalCount_le_dyadicLength (D a j : ℕ) :
    residuePrimeIntervalCount D a (dyadicLength j * D)
      (2 * dyadicLength j * D) ≤ dyadicLength j := by
  by_cases hD : D = 0
  · subst D
    simp [residuePrimeIntervalCount, residuePrimeIntervalSet]
  · have hDPos : 0 < D := Nat.pos_of_ne_zero hD
    by_cases hcop : D.Coprime a
    · calc
        residuePrimeIntervalCount D a (dyadicLength j * D)
            (2 * dyadicLength j * D) ≤
            ((dyadicProgression D a j hDPos hcop).primeParameterSet
              (dyadicLength j)).card :=
          residuePrimeIntervalCount_le_primeParameterSet hDPos hcop
        _ ≤ (Finset.range (dyadicLength j)).card := by
          apply Finset.card_le_card
          exact Finset.filter_subset _ _
        _ = dyadicLength j := Finset.card_range _
    · rw [residuePrimeIntervalCount_eq_zero_of_not_coprime hDPos hcop]
      exact Nat.zero_le _

/-- A completely unconditional baseline.-/
theorem dyadicBrunTitchmarshHypothesis_elementary (D a J : ℕ) :
    DyadicBrunTitchmarshHypothesis (J : ℝ) D a J := by
  intro j hj
  have hjData := Finset.mem_Icc.mp hj
  have hjPos : 0 < j := by omega
  have hN := residuePrimeIntervalCount_le_dyadicLength D a j
  have hendpoint : 2 ^ (j + 1) * D = 2 * dyadicLength j * D := by
    unfold dyadicLength
    rw [pow_succ]
    ring
  rw [hendpoint]
  rw [show 2 ^ j = dyadicLength j by rfl]
  rw [show (2 : ℝ) ^ j = (dyadicLength j : ℝ) by
    norm_num [dyadicLength]]
  change (residuePrimeIntervalCount D a (dyadicLength j * D)
      (2 * dyadicLength j * D) : ℝ) ≤
    (J : ℝ) * ((dyadicLength j : ℝ) * D) /
      ((D.totient : ℝ) * j)
  have hcount :
      (residuePrimeIntervalCount D a (dyadicLength j * D)
        (2 * dyadicLength j * D) : ℝ) ≤ dyadicLength j := by
    exact_mod_cast hN
  by_cases hD : D = 0
  · subst D
    simp [residuePrimeIntervalCount, residuePrimeIntervalSet]
  · have hDPos : 0 < D := Nat.pos_of_ne_zero hD
    have hphiPos : (0 : ℝ) < D.totient := by
      exact_mod_cast Nat.totient_pos.mpr hDPos
    have hjRealPos : (0 : ℝ) < j := by exact_mod_cast hjPos
    have hden : 0 < (D.totient : ℝ) * j := mul_pos hphiPos hjRealPos
    refine hcount.trans ?_
    apply (le_div_iff₀ hden).mpr
    have hphiD : (D.totient : ℝ) ≤ D := by exact_mod_cast Nat.totient_le D
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hjData.2
    have hN0 : (0 : ℝ) ≤ dyadicLength j := by positivity
    have hD0 : (0 : ℝ) ≤ D := by positivity
    calc
      (dyadicLength j : ℝ) * ((D.totient : ℝ) * j) =
          (dyadicLength j : ℝ) * D.totient * j := by ring
      _ ≤ (dyadicLength j : ℝ) * D * j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphiD hN0) hjRealPos.le
      _ ≤ (dyadicLength j : ℝ) * D * J := by
        exact mul_le_mul_of_nonneg_left hjJ (mul_nonneg hN0 hD0)
      _ = (J : ℝ) * ((dyadicLength j : ℝ) * D) := by ring

/-! ## Reduction of the uniform dyadic bound -/

/-- Direct Mertens-product hypothesis at each dyadic progression cutoff.-/
def DyadicDirectMertensUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) (J : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 2 J,
    BFPSTwoAffine.directMertensProduct (cutoff (dyadicLength j)) ≤ C / j

/-- Condition ensuring the sieve cutoff lies below the dyadic interval.-/
def DyadicCutoffBelowInterval
    (cutoff : ℕ → ℕ) (D J : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 2 J, cutoff (dyadicLength j) ≤ dyadicLength j * D

/-- Euler's elementary Mertens-product estimate is already strong enough for the dyadic local-product input at the identity cutoff, with its exact change-of-base constant.-/
theorem dyadicDirectMertensUpperBound_id (J : ℕ) :
    DyadicDirectMertensUpperBound id (Real.log 2)⁻¹ J := by
  intro j hj
  have hjData := Finset.mem_Icc.mp hj
  have hjPos : 0 < j := by omega
  have hN3 : 3 ≤ dyadicLength j := by
    have hpow : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjData.1
    change 3 ≤ 2 ^ j
    norm_num at hpow ⊢
    omega
  have hM := BFPSTwoAffine.directMertensProductUpperBound_id
    (dyadicLength j) hN3
  change BFPSTwoAffine.directMertensProduct (dyadicLength j) ≤
    (Real.log 2)⁻¹ / j
  calc
    BFPSTwoAffine.directMertensProduct (dyadicLength j) ≤
        1 / Real.log (dyadicLength j) := by simpa using hM
    _ = 1 / ((j : ℝ) * Real.log 2) := by
      congr 2
      rw [show (dyadicLength j : ℝ) = (2 : ℝ) ^ j by
        norm_num [dyadicLength], Real.log_pow]
    _ = (Real.log 2)⁻¹ / j := by
      have hjNe : (j : ℝ) ≠ 0 := by positivity
      have hlogNe : Real.log (2 : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num))
      field_simp

theorem dyadicCutoffBelowInterval_id {D J : ℕ} (hD : 0 < D) :
    DyadicCutoffBelowInterval id D J := by
  intro j _hj
  change dyadicLength j ≤ dyadicLength j * D
  exact Nat.le_mul_of_pos_right (dyadicLength j) hD

end BrunTitchmarsh

end

end RankAmplification
