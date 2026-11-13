import Tengoku.Rankamplificationtotient.RankAmplification.AffinePrimePairs
import Tengoku.Seed.NumberTheory.SelbergSieve
import Tengoku.Seed.NumberTheory.Primorial
import Tengoku.Seed.Data.Int.CardIntervalMod
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Selberg-sieve reduction for two affine forms This file constructs the finite sieve problem attached to `(A*r+1)(B*r+1)` and proves its exact residue-count error formula. -/

namespace RankAmplification

open Finset Nat ArithmeticFunction

noncomputable section

namespace AffinePrimePair

variable (L : AffinePrimePair)

/-- Product of the two affine forms.-/
def productValue (r : ℕ) : ℕ :=
  L.leftValue r * L.rightValue r

theorem productValue_pos (r : ℕ) : 0 < L.productValue r :=
  mul_pos (L.value_pos r).1 (L.value_pos r).2

theorem productValue_strictMono : StrictMono L.productValue := by
  intro r s hrs
  have hleft := L.value_strictMono_left hrs
  have hright := L.value_strictMono_right hrs
  have hleftPos := (L.value_pos r).1
  have hrightPos := (L.value_pos r).2
  unfold productValue
  nlinarith

/-- Encode the parameters `r=1,...,R` by `t=0,...,R-1`.-/
def shiftedProductValue (t : ℕ) : ℕ :=
  L.productValue (t + 1)

theorem shiftedProductValue_strictMono : StrictMono L.shiftedProductValue := by
  intro r s hrs
  exact L.productValue_strictMono (Nat.add_lt_add_right hrs 1)

/-- The shifted product as a natural-number embedding, so the sieve support has no multiplicity.-/
def shiftedProductEmbedding : ℕ ↪ ℕ where
  toFun := L.shiftedProductValue
  inj' := L.shiftedProductValue_strictMono.injective

/-- The finite set of product values attached to `1 ≤ r ≤ R`.-/
def selbergSupport (R : ℕ) : Finset ℕ :=
  (Finset.range R).map L.shiftedProductEmbedding

@[simp]
theorem mem_selbergSupport {R N : ℕ} :
    N ∈ L.selbergSupport R ↔ ∃ t < R, L.shiftedProductValue t = N := by
  simp [selbergSupport, shiftedProductEmbedding]

/-- Evaluation of the shifted product in `ZMod d`.-/
def shiftedProductMod (d : ℕ) (t : ZMod d) : ZMod d :=
  ((L.leftSlope : ZMod d) * (t + 1) + 1) *
    ((L.rightSlope : ZMod d) * (t + 1) + 1)

/-- Bad parameter residues modulo `d`, represented by `Fin d`.-/
def shiftedBadResidueSet (d : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun t ↦ d ∣ L.shiftedProductValue t

@[simp]
theorem mem_shiftedBadResidueSet {d : ℕ} {t : Fin d} :
    t ∈ L.shiftedBadResidueSet d ↔ d ∣ L.shiftedProductValue t := by
  simp [shiftedBadResidueSet]

/-- Number of bad residues modulo `d`.-/
def shiftedBadResidueCount (d : ℕ) : ℕ :=
  (L.shiftedBadResidueSet d).card

/-- Divisibility by `d` is exactly vanishing of the shifted product modulo `d`.-/
theorem shiftedProductMod_natCast_eq_zero_iff_dvd (d t : ℕ) :
    L.shiftedProductMod d t = 0 ↔ d ∣ L.shiftedProductValue t := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [shiftedProductMod, shiftedProductValue, productValue, leftValue, rightValue,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- Translation by one identifies shifted bad residues with the existing local bad-residue set.-/
theorem shiftedBadResidueCount_eq_badResidueSet_card {p : ℕ} (hp : p.Prime) :
    L.shiftedBadResidueCount p = (L.badResidueSet p hp).card := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let e : Fin p ≃ ZMod p :=
    (ZMod.finEquiv p).toEquiv.trans (Equiv.addRight 1)
  have he (t : Fin p) :
      t ∈ L.shiftedBadResidueSet p ↔ e t ∈ L.badResidueSet p hp := by
    rw [mem_shiftedBadResidueSet, mem_badResidueSet_iff (L := L) hp,
      ← L.shiftedProductMod_natCast_eq_zero_iff_dvd p t]
    have hfin : (ZMod.finEquiv p) t = (t.val : ZMod p) := by
      cases p with
      | zero => exact Fin.elim0 t
      | succ p =>
          change t = (t.val : ZMod (p + 1))
          exact (ZMod.natCast_zmod_val (n := p + 1) t).symm
    have hfin' : (ZMod.finEquiv p).toEquiv t = (t.val : ZMod p) := hfin
    simp only [e, Equiv.trans_apply, Equiv.coe_addRight]
    rw [hfin']
    rfl
  have rootEquiv :
      {t // t ∈ L.shiftedBadResidueSet p} ≃
        {u // u ∈ L.badResidueSet p hp} :=
    e.subtypeEquiv he
  calc
    L.shiftedBadResidueCount p =
        Fintype.card {t // t ∈ L.shiftedBadResidueSet p} := by
      rw [shiftedBadResidueCount, Fintype.card_coe]
    _ = Fintype.card {u // u ∈ L.badResidueSet p hp} :=
      Fintype.card_congr rootEquiv
    _ = (L.badResidueSet p hp).card := Fintype.card_coe _

theorem shiftedBadResidueCount_le_two {p : ℕ} (hp : p.Prime) :
    L.shiftedBadResidueCount p ≤ 2 := by
  rw [L.shiftedBadResidueCount_eq_badResidueSet_card hp]
  exact L.card_badResidueSet_le_two hp

/-- For this special pair of constant-one forms the two local roots coincide modulo `2`, so the local density is strictly below one for every prime.-/
theorem shiftedBadResidueCount_lt_prime {p : ℕ} (hp : p.Prime) :
    L.shiftedBadResidueCount p < p := by
  by_cases hpTwo : p = 2
  · subst p
    rw [L.shiftedBadResidueCount_eq_badResidueSet_card Nat.prime_two]
    apply lt_of_le_of_lt _ (by norm_num : 1 < 2)
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxEq := (L.mem_badResidueSet_iff Nat.prime_two).mp hx
    have hyEq := (L.mem_badResidueSet_iff Nat.prime_two).mp hy
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      norm_num at hxEq
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      norm_num at hyEq
    apply ZMod.val_injective 2
    have hxVal0 : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx0
    have hyVal0 : y.val ≠ 0 := (ZMod.val_eq_zero y).not.mpr hy0
    have hxValLt := ZMod.val_lt x
    have hyValLt := ZMod.val_lt y
    omega
  · exact (L.shiftedBadResidueCount_le_two hp).trans_lt (by
      have hpTwoLe := hp.two_le
      omega)

/-! ## Exact residue-class counting -/

/-- The shifted product respects congruences in its parameter.-/
theorem shiftedProductValue_modEq {d t u : ℕ} (htu : t ≡ u [MOD d]) :
    L.shiftedProductValue t ≡ L.shiftedProductValue u [MOD d] := by
  rw [← ZMod.natCast_eq_natCast_iff] at htu ⊢
  simp only [shiftedProductValue, productValue, leftValue, rightValue, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [htu]

/-- Parameters below `R` for which the affine product is divisible by `d`.-/
def divisibleParameterSet (R d : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ d ∣ L.shiftedProductValue t

@[simp]
theorem mem_divisibleParameterSet {R d t : ℕ} :
    t ∈ L.divisibleParameterSet R d ↔ t < R ∧ d ∣ L.shiftedProductValue t := by
  simp [divisibleParameterSet]

/-- One residue-class fibre in `[0,R)`.-/
def parameterResidueFiber (R d : ℕ) (a : Fin d) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ t ≡ a.val [MOD d]

@[simp]
theorem mem_parameterResidueFiber {R d : ℕ} {a : Fin d} {t : ℕ} :
    t ∈ parameterResidueFiber R d a ↔ t < R ∧ t ≡ a.val [MOD d] := by
  simp [parameterResidueFiber]

/-- Exact size of one residue fibre.-/
theorem card_parameterResidueFiber {R d : ℕ} (hd : 0 < d) (a : Fin d) :
    (parameterResidueFiber R d a).card =
      R / d + if a.val < R % d then 1 else 0 := by
  rw [parameterResidueFiber, ← Nat.count_eq_card_filter_range]
  simpa only [Nat.mod_eq_of_lt a.isLt] using Nat.count_modEq_card R hd a.val

/-- Number of bad residues that occur once more in the final incomplete block.-/
def residueExcessCount (R d : ℕ) : ℕ :=
  ((L.shiftedBadResidueSet d).filter fun a ↦ a.val < R % d).card

theorem residueExcessCount_le (R d : ℕ) :
    L.residueExcessCount R d ≤ L.shiftedBadResidueCount d := by
  exact Finset.card_filter_le _ _

/-- The divisible parameters are the disjoint union of their bad residue fibres.-/
theorem divisibleParameterSet_eq_biUnion {R d : ℕ} (hd : 0 < d) :
    L.divisibleParameterSet R d =
      (L.shiftedBadResidueSet d).biUnion (parameterResidueFiber R d) := by
  ext t
  rw [mem_divisibleParameterSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨htR, htDiv⟩
    let a : Fin d := ⟨t % d, Nat.mod_lt t hd⟩
    have hta : t ≡ a.val [MOD d] := (Nat.mod_modEq t d).symm
    have hvalue := L.shiftedProductValue_modEq hta
    have haDiv : d ∣ L.shiftedProductValue a.val :=
      Nat.modEq_zero_iff_dvd.mp (hvalue.symm.trans htDiv.modEq_zero_nat)
    exact ⟨a, by simpa [shiftedBadResidueSet] using haDiv,
      mem_parameterResidueFiber.mpr ⟨htR, hta⟩⟩
  · rintro ⟨a, haRoot, hta⟩
    have htaData := mem_parameterResidueFiber.mp hta
    have haDiv : d ∣ L.shiftedProductValue a := by
      simpa [shiftedBadResidueSet] using haRoot
    have hvalue := L.shiftedProductValue_modEq htaData.2
    exact ⟨htaData.1,
      Nat.modEq_zero_iff_dvd.mp (hvalue.trans haDiv.modEq_zero_nat)⟩

theorem parameterResidueFiber_pairwiseDisjoint (R d : ℕ) :
    ((L.shiftedBadResidueSet d : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint
      (parameterResidueFiber R d) := by
  intro a _ha b _hb hab
  change Disjoint (parameterResidueFiber R d a) (parameterResidueFiber R d b)
  rw [Finset.disjoint_left]
  intro t hta htb
  have hat := (mem_parameterResidueFiber.mp hta).2
  have hbt := (mem_parameterResidueFiber.mp htb).2
  apply hab
  apply Fin.ext
  have habMod : a.val ≡ b.val [MOD d] := hat.symm.trans hbt
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using habMod

/-- Exact residue-count formula, including the incomplete final block.-/
theorem card_divisibleParameterSet_eq {R d : ℕ} (hd : 0 < d) :
    (L.divisibleParameterSet R d).card =
      L.shiftedBadResidueCount d * (R / d) + L.residueExcessCount R d := by
  rw [L.divisibleParameterSet_eq_biUnion hd,
    Finset.card_biUnion (L.parameterResidueFiber_pairwiseDisjoint R d)]
  simp_rw [card_parameterResidueFiber hd]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const_nat, shiftedBadResidueCount, residueExcessCount,
    Finset.card_filter]

/-- Real form of the exact count error `r_d`, with `0 ≤ r_d ≤ ν(d)`.-/
theorem card_divisibleParameterSet_cast_eq_main_add_error {R d : ℕ} (hd : 0 < d) :
    ((L.divisibleParameterSet R d).card : ℝ) =
      (L.shiftedBadResidueCount d : ℝ) * (R / d : ℕ) +
        L.residueExcessCount R d := by
  exact_mod_cast L.card_divisibleParameterSet_eq hd

theorem residueExcessCount_cast_le (R d : ℕ) :
    (L.residueExcessCount R d : ℝ) ≤ L.shiftedBadResidueCount d := by
  exact_mod_cast L.residueExcessCount_le R d

/-! ## The finite Selberg-sieve datum -/

/-- The local density attached to the two affine roots modulo `p`.-/
def localDensity (p : ℕ) : ℝ :=
  (L.shiftedBadResidueCount p : ℝ) / p

/-- The squarefree multiplicative extension of the local densities.-/
def sieveDensity : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors L.localDensity

theorem sieveDensity_isMultiplicative : L.sieveDensity.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors L.localDensity

@[simp]
theorem sieveDensity_apply_prime {p : ℕ} (hp : p.Prime) :
    L.sieveDensity p = L.localDensity p := by
  rw [sieveDensity, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp.primeFactors]

/-- Only primes which actually remove a residue class are put into the sieve product.-/
def activePrimeSet (z : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter fun p ↦ 0 < L.shiftedBadResidueCount p

@[simp]
theorem mem_activePrimeSet {z p : ℕ} :
    p ∈ L.activePrimeSet z ↔
      p.Prime ∧ p ≤ z ∧ 0 < L.shiftedBadResidueCount p := by
  simp only [activePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  aesop

/-- Product of the active sifting primes up to `z`.-/
def activePrimeProduct (z : ℕ) : ℕ :=
  ∏ p ∈ L.activePrimeSet z, p

theorem activePrimeProduct_squarefree (z : ℕ) : Squarefree (L.activePrimeProduct z) := by
  rw [activePrimeProduct]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq ↦ ?_)
    (fun p hp ↦ (L.mem_activePrimeSet.mp hp).1.squarefree)
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (L.mem_activePrimeSet.mp hp).1
    (L.mem_activePrimeSet.mp hq).1).mpr hpq

theorem prime_dvd_activePrimeProduct_iff {z p : ℕ} (hp : p.Prime) :
    p ∣ L.activePrimeProduct z ↔ p ∈ L.activePrimeSet z := by
  constructor
  · intro hpd
    rw [activePrimeProduct, hp.prime.dvd_finsetProd_iff] at hpd
    obtain ⟨q, hq, hpq⟩ := hpd
    have hqPrime := (L.mem_activePrimeSet.mp hq).1
    have hpEq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq
    simpa [hpEq] using hq
  · intro hpMem
    exact dvd_prod_of_mem _ hpMem

/-- A prime with no bad residue divides no shifted affine product.-/
theorem not_dvd_shiftedProductValue_of_count_eq_zero {p t : ℕ} (hp : p.Prime)
    (hcount : L.shiftedBadResidueCount p = 0) :
    ¬p ∣ L.shiftedProductValue t := by
  intro hdiv
  let a : Fin p := ⟨t % p, Nat.mod_lt t hp.pos⟩
  have hta : t ≡ a.val [MOD p] := (Nat.mod_modEq t p).symm
  have hvalue := L.shiftedProductValue_modEq hta
  have haDiv : p ∣ L.shiftedProductValue a.val :=
    Nat.modEq_zero_iff_dvd.mp (hvalue.symm.trans hdiv.modEq_zero_nat)
  have haMem : a ∈ L.shiftedBadResidueSet p := by
    simpa using haDiv
  have hne : L.shiftedBadResidueCount p ≠ 0 := by
    rw [shiftedBadResidueCount]
    exact Finset.card_ne_zero.mpr ⟨a, haMem⟩
  exact hne hcount

/-- Concrete `BoundingSieve` for the product values with unit weights.-/
def affineBoundingSieve (R z : ℕ) : BoundingSieve where
  support := L.selbergSupport R
  prodPrimes := L.activePrimeProduct z
  prodPrimes_squarefree := L.activePrimeProduct_squarefree z
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ by norm_num
  totalMass := R
  nu := L.sieveDensity
  nu_mult := L.sieveDensity_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpd
    have hpMem := (L.prime_dvd_activePrimeProduct_iff hp).mp hpd
    have hpData : p.Prime ∧ p ≤ z ∧ 0 < L.shiftedBadResidueCount p :=
      L.mem_activePrimeSet.mp hpMem
    rw [L.sieveDensity_apply_prime hp]
    unfold localDensity
    exact div_pos (by exact_mod_cast hpData.2.2) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpd
    rw [L.sieveDensity_apply_prime hp]
    unfold localDensity
    rw [div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast L.shiftedBadResidueCount_lt_prime hp

/-- Adding a legitimate level turns the datum into Mathlib's `SelbergSieve`.-/
def affineSelbergSieve (R z : ℕ) (level : ℝ) (hlevel : 1 ≤ level) : SelbergSieve where
  toBoundingSieve := L.affineBoundingSieve R z
  level := level
  one_le_level := hlevel

/-- The abstract sieve's divisibility sum is exactly the finite parameter count.-/
theorem affineBoundingSieve_multSum (R z d : ℕ) :
    (L.affineBoundingSieve R z).multSum d =
      (L.divisibleParameterSet R d).card := by
  simp [BoundingSieve.multSum, affineBoundingSieve, selbergSupport,
    shiftedProductEmbedding, divisibleParameterSet]
  rw [Finset.filter_map, Finset.card_map]
  rfl

/-- Hence the abstract remainder has a completely explicit finite meaning.-/
theorem affineBoundingSieve_rem (R z d : ℕ) :
    (L.affineBoundingSieve R z).rem d =
      (L.divisibleParameterSet R d).card - L.sieveDensity d * R := by
  rw [BoundingSieve.rem, L.affineBoundingSieve_multSum]
  rfl

/-- Exact remainder formula after splitting `[0,R)` into complete residue blocks.-/
theorem affineBoundingSieve_rem_eq_floor_add_excess {R z d : ℕ} (hd : 0 < d) :
    (L.affineBoundingSieve R z).rem d =
      (L.shiftedBadResidueCount d : ℝ) * (R / d : ℕ) +
        L.residueExcessCount R d - L.sieveDensity d * R := by
  rw [L.affineBoundingSieve_rem, L.card_divisibleParameterSet_cast_eq_main_add_error hd]

/-- At a prime modulus, the remainder is the incomplete-block excess minus the exact fractional part of the local main term.-/
theorem affineBoundingSieve_rem_prime {R z p : ℕ} (hp : p.Prime) :
    (L.affineBoundingSieve R z).rem p =
      (L.residueExcessCount R p : ℝ) -
        (L.shiftedBadResidueCount p : ℝ) * (R % p : ℕ) / p := by
  rw [L.affineBoundingSieve_rem_eq_floor_add_excess hp.pos,
    L.sieveDensity_apply_prime hp]
  unfold localDensity
  have hR : (R : ℝ) = (p : ℝ) * (R / p : ℕ) + (R % p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div R p).symm.trans (by omega)
  rw [hR]
  have hpCast : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

/-- The exact prime-modulus remainder has the classical local bound `|r_p| ≤ ν(p)`.-/
theorem abs_affineBoundingSieve_rem_prime_le {R z p : ℕ} (hp : p.Prime) :
    |(L.affineBoundingSieve R z).rem p| ≤ L.shiftedBadResidueCount p := by
  rw [L.affineBoundingSieve_rem_prime hp]
  have hpCast : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hk0 : 0 ≤ (L.shiftedBadResidueCount p : ℝ) := by positivity
  have he0 : 0 ≤ (L.residueExcessCount R p : ℝ) := by positivity
  have hek : (L.residueExcessCount R p : ℝ) ≤ L.shiftedBadResidueCount p :=
    L.residueExcessCount_cast_le R p
  have hfrac0 : 0 ≤ ((R % p : ℕ) : ℝ) / p := div_nonneg (by positivity) hpCast.le
  have hfrac1 : ((R % p : ℕ) : ℝ) / p ≤ 1 := by
    rw [div_le_one hpCast]
    exact_mod_cast (Nat.mod_lt R hp.pos).le
  have hterm0 : 0 ≤
      (L.shiftedBadResidueCount p : ℝ) * (R % p : ℕ) / p := by positivity
  have htermk :
      (L.shiftedBadResidueCount p : ℝ) * (R % p : ℕ) / p ≤
        L.shiftedBadResidueCount p := by
    calc
      (L.shiftedBadResidueCount p : ℝ) * (R % p : ℕ) / p =
          (L.shiftedBadResidueCount p : ℝ) * (((R % p : ℕ) : ℝ) / p) := by ring
      _ ≤ (L.shiftedBadResidueCount p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfrac1 hk0
      _ = L.shiftedBadResidueCount p := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ## Identifying the sifted set -/

theorem coprime_activePrimeProduct_iff {z t : ℕ} :
    Nat.Coprime (L.activePrimeProduct z) (L.shiftedProductValue t) ↔
      ∀ p ∈ Nat.primesLE z, ¬p ∣ L.shiftedProductValue t := by
  constructor
  · intro hcop p hpz
    have hp : p.Prime := Nat.prime_of_mem_primesLE hpz
    by_cases hactive : 0 < L.shiftedBadResidueCount p
    · have hpMem : p ∈ L.activePrimeSet z := L.mem_activePrimeSet.mpr
        ⟨hp, Nat.le_of_mem_primesLE hpz, hactive⟩
      have hpcop : Nat.Coprime p (L.shiftedProductValue t) := by
        rw [activePrimeProduct, Nat.coprime_prod_left_iff] at hcop
        exact hcop p hpMem
      exact hp.coprime_iff_not_dvd.mp hpcop
    · have hzero : L.shiftedBadResidueCount p = 0 := Nat.eq_zero_of_not_pos hactive
      exact L.not_dvd_shiftedProductValue_of_count_eq_zero hp hzero
  · intro hall
    rw [activePrimeProduct, Nat.coprime_prod_left_iff]
    intro p hpMem
    have hpData := L.mem_activePrimeSet.mp hpMem
    exact hpData.1.coprime_iff_not_dvd.mpr
      (hall p (Nat.mem_primesLE.mpr ⟨hpData.2.1, hpData.1⟩))

/-- Sifted parameters in the zero-based encoding.-/
def siftedParameterSet (R z : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦
    Nat.Coprime (L.activePrimeProduct z) (L.shiftedProductValue t)

@[simp]
theorem mem_siftedParameterSet {R z t : ℕ} :
    t ∈ L.siftedParameterSet R z ↔
      t < R ∧ Nat.Coprime (L.activePrimeProduct z) (L.shiftedProductValue t) := by
  simp [siftedParameterSet]

/-- The translation from zero-based parameters to the paper's `1 ≤ r ≤ R` convention.-/
def parameterShiftEmbedding : ℕ ↪ ℕ where
  toFun t := t + 1
  inj' := fun _ _ h ↦ Nat.add_right_cancel h

@[simp]
theorem parameterShiftEmbedding_apply (t : ℕ) : parameterShiftEmbedding t = t + 1 := rfl

/-- The abstract sifted parameters and the pre-existing paper-style sifted set agree exactly.-/
theorem siftedPairSet_eq_map (R z : ℕ) :
    L.siftedPairSet R z =
      (L.siftedParameterSet R z).map parameterShiftEmbedding := by
  ext r
  constructor
  · intro hr
    have hrData := L.mem_siftedPairSet.mp hr
    have hrShift : r - 1 + 1 = r := by omega
    rw [Finset.mem_map]
    refine ⟨r - 1, ?_, ?_⟩
    · apply L.mem_siftedParameterSet.mpr
      refine ⟨by omega, ?_⟩
      rw [L.coprime_activePrimeProduct_iff]
      simpa [shiftedProductValue, productValue, hrShift] using hrData.2.2
    · simp only [parameterShiftEmbedding_apply, hrShift]
  · intro hr
    rw [Finset.mem_map] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have htData := L.mem_siftedParameterSet.mp ht
    apply L.mem_siftedPairSet.mpr
    refine ⟨by change 1 ≤ t + 1; omega, by change t + 1 ≤ R; omega, ?_⟩
    rw [L.coprime_activePrimeProduct_iff] at htData
    simpa [parameterShiftEmbedding_apply, shiftedProductValue, productValue] using htData.2

/-! ## Removing the small-prime-value exceptions -/

/-- Prime pairs for which the left affine value does not exceed the sieve cutoff.-/
def leftSmallPrimePairSet (R z : ℕ) : Finset ℕ :=
  (L.primePairSet R).filter fun r ↦ L.leftValue r ≤ z

@[simp]
theorem mem_leftSmallPrimePairSet {R z r : ℕ} :
    r ∈ L.leftSmallPrimePairSet R z ↔
      r ∈ L.primePairSet R ∧ L.leftValue r ≤ z := by
  simp [leftSmallPrimePairSet]

/-- Prime pairs for which the right affine value does not exceed the sieve cutoff.-/
def rightSmallPrimePairSet (R z : ℕ) : Finset ℕ :=
  (L.primePairSet R).filter fun r ↦ L.rightValue r ≤ z

@[simp]
theorem mem_rightSmallPrimePairSet {R z r : ℕ} :
    r ∈ L.rightSmallPrimePairSet R z ↔
      r ∈ L.primePairSet R ∧ L.rightValue r ≤ z := by
  simp [rightSmallPrimePairSet]

/-- Strict monotonicity gives the elementary `O(z)` bound for left-value exceptions.-/
theorem card_leftSmallPrimePairSet_le (R z : ℕ) :
    (L.leftSmallPrimePairSet R z).card ≤ z + 1 := by
  rw [← Finset.card_range (z + 1)]
  refine Finset.card_le_card_of_injOn L.leftValue ?_ ?_
  · intro r hr
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
      (L.mem_leftSmallPrimePairSet.mp hr).2)
  · intro a _ha b _hb hab
    exact L.value_strictMono_left.injective hab

/-- Strict monotonicity gives the elementary `O(z)` bound for right-value exceptions.-/
theorem card_rightSmallPrimePairSet_le (R z : ℕ) :
    (L.rightSmallPrimePairSet R z).card ≤ z + 1 := by
  rw [← Finset.card_range (z + 1)]
  refine Finset.card_le_card_of_injOn L.rightValue ?_ ?_
  · intro r hr
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
      (L.mem_rightSmallPrimePairSet.mp hr).2)
  · intro a _ha b _hb hab
    exact L.value_strictMono_right.injective hab

/-- Every prime pair either survives the sieve or has a prime value at most `z`.-/
theorem primePairSet_subset_sifted_union_small (R z : ℕ) :
    L.primePairSet R ⊆
      (L.siftedPairSet R z ∪ L.leftSmallPrimePairSet R z) ∪
        L.rightSmallPrimePairSet R z := by
  intro r hr
  by_cases hleft : z < L.leftValue r
  · by_cases hright : z < L.rightValue r
    · have hsift := L.mem_siftedPairSet_of_prime_values_gt hr hleft hright
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hsift)))
    · have hsmall : r ∈ L.rightSmallPrimePairSet R z :=
        L.mem_rightSmallPrimePairSet.mpr ⟨hr, Nat.le_of_not_gt hright⟩
      exact Finset.mem_union.mpr (Or.inr hsmall)
  · have hsmall : r ∈ L.leftSmallPrimePairSet R z :=
      L.mem_leftSmallPrimePairSet.mpr ⟨hr, Nat.le_of_not_gt hleft⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hsmall)))

/-- Exact finite reduction: the prime-pair count is at most the sifted count plus `2(z+1)`.-/
theorem card_primePairSet_le_sifted_add (R z : ℕ) :
    (L.primePairSet R).card ≤ (L.siftedPairSet R z).card + 2 * (z + 1) := by
  calc
    (L.primePairSet R).card ≤
        ((L.siftedPairSet R z ∪ L.leftSmallPrimePairSet R z) ∪
          L.rightSmallPrimePairSet R z).card :=
      Finset.card_le_card (L.primePairSet_subset_sifted_union_small R z)
    _ ≤ (L.siftedPairSet R z ∪ L.leftSmallPrimePairSet R z).card +
        (L.rightSmallPrimePairSet R z).card := Finset.card_union_le _ _
    _ ≤ ((L.siftedPairSet R z).card + (L.leftSmallPrimePairSet R z).card) +
        (L.rightSmallPrimePairSet R z).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((L.siftedPairSet R z).card + (z + 1)) + (z + 1) :=
      Nat.add_le_add
        (Nat.add_le_add_left (L.card_leftSmallPrimePairSet_le R z) _)
        (L.card_rightSmallPrimePairSet_le R z)
    _ = (L.siftedPairSet R z).card + 2 * (z + 1) := by omega

/-! ## Honest analytic endpoint -/

/-- The logarithmic scale in the conclusion of paper Lemma 9.5.-/
def logSquaredScale (R : ℕ) : ℝ :=
  (R : ℝ) / (Real.log R) ^ 2

/-- The terminal dimension-two sieve estimate.-/
def DimensionTwoSelbergUpperBound (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ R, 3 ≤ R →
    (L.affineBoundingSieve R (cutoff R)).siftedSum ≤ C * logSquaredScale R

/-- The independent elementary-growth requirement on the chosen cutoff.-/
def CutoffExceptionUpperBound (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ R, 3 ≤ R →
    ((2 * (cutoff R + 1) : ℕ) : ℝ) ≤ C * logSquaredScale R

/-- The paper's fixed-form `R/(log R)^2` conclusion, as an explicit proposition.-/
def HasLogSquaredPrimePairBound : Prop :=
  ∃ C : ℝ, ∀ R, 3 ≤ R →
    ((L.primePairSet R).card : ℝ) ≤ C * logSquaredScale R

end AffinePrimePair

end

end RankAmplification
