import Tengoku.Rankamplificationtotient.RankAmplification.BFPSPrimePredecessorReduction
import Tengoku.Rankamplificationtotient.RankAmplification.AffineSelbergReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Selberg reduction for the BFPS forms `q` and `m*q+1` The diagonal affine sieve has constant terms `(1,1)`. -/

namespace RankAmplification

open Finset Nat ArithmeticFunction
open scoped BigOperators Nat.Prime

noncomputable section

namespace BFPSTwoAffine

/-! ## Product values and local roots -/

/-- Product of the BFPS linear forms.-/
def productValue (m q : ℕ) : ℕ := q * (m * q + 1)

theorem productValue_pos (m q : ℕ) (hq : 0 < q) : 0 < productValue m q := by
  unfold productValue
  positivity

theorem productValue_strictMono (m : ℕ) : StrictMono (productValue m) := by
  intro q r hqr
  have hright : m * q + 1 ≤ m * r + 1 := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_left m hqr.le) 1
  calc
    productValue m q = q * (m * q + 1) := rfl
    _ < r * (m * q + 1) := Nat.mul_lt_mul_of_pos_right hqr (by omega)
    _ ≤ r * (m * r + 1) := Nat.mul_le_mul_left r hright
    _ = productValue m r := rfl

/-- Zero-based encoding `q=t+1`.-/
def shiftedProductValue (m t : ℕ) : ℕ := productValue m (t + 1)

theorem shiftedProductValue_strictMono (m : ℕ) : StrictMono (shiftedProductValue m) := by
  intro t u htu
  exact productValue_strictMono m (Nat.add_lt_add_right htu 1)

/-- Embedding of zero-based parameters into their shifted product values.-/
def shiftedProductEmbedding (m : ℕ) : ℕ ↪ ℕ where
  toFun := shiftedProductValue m
  inj' := (shiftedProductValue_strictMono m).injective

/-- Product-value support attached to `1 ≤ q ≤ R`.-/
def selbergSupport (m R : ℕ) : Finset ℕ :=
  (Finset.range R).map (shiftedProductEmbedding m)

@[simp]
theorem mem_selbergSupport {m R N : ℕ} :
    N ∈ selbergSupport m R ↔ ∃ t < R, shiftedProductValue m t = N := by
  simp [selbergSupport, shiftedProductEmbedding]

/-- Shifted product polynomial evaluated modulo `d`.-/
def shiftedProductMod (m d : ℕ) (t : ZMod d) : ZMod d :=
  (t + 1) * ((m : ZMod d) * (t + 1) + 1)

/-- Residue classes modulo `d` on which the shifted product vanishes.-/
def shiftedBadResidueSet (m d : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun t ↦ d ∣ shiftedProductValue m t

@[simp]
theorem mem_shiftedBadResidueSet {m d : ℕ} {t : Fin d} :
    t ∈ shiftedBadResidueSet m d ↔ d ∣ shiftedProductValue m t := by
  simp [shiftedBadResidueSet]

/-- Number of bad shifted-product residue classes modulo `d`.-/
def shiftedBadResidueCount (m d : ℕ) : ℕ :=
  (shiftedBadResidueSet m d).card

theorem shiftedProductMod_natCast_eq_zero_iff_dvd (m d t : ℕ) :
    shiftedProductMod m d t = 0 ↔ d ∣ shiftedProductValue m t := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [shiftedProductMod, shiftedProductValue, productValue,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- The unshifted roots are `q=0` together with roots of `m*q+1`.-/
def badResidueSet (m p : ℕ) (hp : p.Prime) : Finset (ZMod p) :=
  {0} ∪ AffinePrimePair.affineRootSet p m hp

@[simp]
theorem mem_badResidueSet_iff {m p : ℕ} (hp : p.Prime) {q : ZMod p} :
    q ∈ badResidueSet m p hp ↔ q * ((m : ZMod p) * q + 1) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [badResidueSet, AffinePrimePair.mem_affineRootSet]

theorem zero_disjoint_affineRootSet {m p : ℕ} (hp : p.Prime) :
    Disjoint ({0} : Finset (ZMod p)) (AffinePrimePair.affineRootSet p m hp) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Finset.disjoint_left]
  intro q hqZero hqRoot
  have hq : q = 0 := Finset.mem_singleton.mp hqZero
  subst q
  have hroot := (AffinePrimePair.mem_affineRootSet hp).mp hqRoot
  norm_num at hroot

theorem affineRootSet_eq_empty_of_prime_dvd {m p : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) :
    AffinePrimePair.affineRootSet p m hp = ∅ := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have hroot := (AffinePrimePair.mem_affineRootSet hp).mp hq
  have hmzero : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
  rw [hmzero, zero_mul, zero_add] at hroot
  exact one_ne_zero hroot

theorem card_affineRootSet_eq_one_of_prime_not_dvd {m p : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) :
    (AffinePrimePair.affineRootSet p m hp).card = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm : (m : ZMod p) ≠ 0 := by
    intro hmzero
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hmzero)
  let q : ZMod p := -(m : ZMod p)⁻¹
  have hq : q ∈ AffinePrimePair.affineRootSet p m hp := by
    rw [AffinePrimePair.mem_affineRootSet hp]
    simp only [q, mul_neg, mul_inv_cancel₀ hm]
    ring
  apply Nat.le_antisymm (AffinePrimePair.card_affineRootSet_le_one hp)
  exact Finset.card_pos.mpr ⟨q, hq⟩

/-- Exact local count: one root at primes dividing `m`, and two roots otherwise.-/
theorem card_badResidueSet {m p : ℕ} (hp : p.Prime) :
    (badResidueSet m p hp).card = if p ∣ m then 1 else 2 := by
  rw [badResidueSet,
    Finset.card_union_of_disjoint (zero_disjoint_affineRootSet hp)]
  by_cases hpm : p ∣ m
  · rw [ite_eq_left hpm, affineRootSet_eq_empty_of_prime_dvd hp hpm]
    simp
  · rw [ite_eq_right hpm, card_affineRootSet_eq_one_of_prime_not_dvd hp hpm]
    simp

/-- Translation by one identifies zero-based parameter residues with the local root set.-/
theorem shiftedBadResidueCount_eq_badResidueSet_card {m p : ℕ} (hp : p.Prime) :
    shiftedBadResidueCount m p = (badResidueSet m p hp).card := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let e : Fin p ≃ ZMod p :=
    (ZMod.finEquiv p).toEquiv.trans (Equiv.addRight 1)
  have he (t : Fin p) :
      t ∈ shiftedBadResidueSet m p ↔ e t ∈ badResidueSet m p hp := by
    rw [mem_shiftedBadResidueSet, mem_badResidueSet_iff hp,
      ← shiftedProductMod_natCast_eq_zero_iff_dvd m p t]
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
      {t // t ∈ shiftedBadResidueSet m p} ≃
        {q // q ∈ badResidueSet m p hp} :=
    e.subtypeEquiv he
  calc
    shiftedBadResidueCount m p =
        Fintype.card {t // t ∈ shiftedBadResidueSet m p} := by
      rw [shiftedBadResidueCount, Fintype.card_coe]
    _ = Fintype.card {q // q ∈ badResidueSet m p hp} :=
      Fintype.card_congr rootEquiv
    _ = (badResidueSet m p hp).card := Fintype.card_coe _

theorem shiftedBadResidueCount_prime {m p : ℕ} (hp : p.Prime) :
    shiftedBadResidueCount m p = if p ∣ m then 1 else 2 := by
  rw [shiftedBadResidueCount_eq_badResidueSet_card hp,
    card_badResidueSet hp]

theorem shiftedBadResidueCount_pos {m p : ℕ} (hp : p.Prime) :
    0 < shiftedBadResidueCount m p := by
  rw [shiftedBadResidueCount_prime hp]
  split <;> omega

theorem shiftedBadResidueCount_le_two {m p : ℕ} (hp : p.Prime) :
    shiftedBadResidueCount m p ≤ 2 := by
  rw [shiftedBadResidueCount_prime hp]
  split <;> omega

/-- Evenness removes the sole saturation obstruction at `p=2`.-/
theorem shiftedBadResidueCount_lt_prime_of_even {m p : ℕ}
    (hm : Even m) (hp : p.Prime) :
    shiftedBadResidueCount m p < p := by
  by_cases hpTwo : p = 2
  · subst p
    have htwoDvd : 2 ∣ m := even_iff_two_dvd.mp hm
    rw [shiftedBadResidueCount_prime Nat.prime_two, ite_eq_left htwoDvd]
    norm_num
  · exact (shiftedBadResidueCount_le_two hp).trans_lt (by
      have hpTwoLe := hp.two_le
      omega)

/-! ## Exact residue counts in an incomplete interval -/

theorem shiftedProductValue_modEq {m d t u : ℕ} (htu : t ≡ u [MOD d]) :
    shiftedProductValue m t ≡ shiftedProductValue m u [MOD d] := by
  rw [← ZMod.natCast_eq_natCast_iff] at htu ⊢
  simp only [shiftedProductValue, productValue, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [htu]

/-- Parameters below `R` whose shifted product is divisible by `d`.-/
def divisibleParameterSet (m R d : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ d ∣ shiftedProductValue m t

@[simp]
theorem mem_divisibleParameterSet {m R d t : ℕ} :
    t ∈ divisibleParameterSet m R d ↔ t < R ∧ d ∣ shiftedProductValue m t := by
  simp [divisibleParameterSet]

/-- Parameters below `R` lying in residue class `a` modulo `d`.-/
def parameterResidueFiber (R d : ℕ) (a : Fin d) : Finset ℕ :=
  (Finset.range R).filter fun t ↦ t ≡ a.val [MOD d]

@[simp]
theorem mem_parameterResidueFiber {R d : ℕ} {a : Fin d} {t : ℕ} :
    t ∈ parameterResidueFiber R d a ↔ t < R ∧ t ≡ a.val [MOD d] := by
  simp [parameterResidueFiber]

theorem card_parameterResidueFiber {R d : ℕ} (hd : 0 < d) (a : Fin d) :
    (parameterResidueFiber R d a).card =
      R / d + if a.val < R % d then 1 else 0 := by
  rw [parameterResidueFiber, ← Nat.count_eq_card_filter_range]
  simpa only [Nat.mod_eq_of_lt a.isLt] using Nat.count_modEq_card R hd a.val

/-- Bad residue classes represented once beyond the complete quotient blocks.-/
def residueExcessCount (m R d : ℕ) : ℕ :=
  ((shiftedBadResidueSet m d).filter fun a ↦ a.val < R % d).card

theorem residueExcessCount_le (m R d : ℕ) :
    residueExcessCount m R d ≤ shiftedBadResidueCount m d :=
  Finset.card_filter_le _ _

theorem divisibleParameterSet_eq_biUnion {m R d : ℕ} (hd : 0 < d) :
    divisibleParameterSet m R d =
      (shiftedBadResidueSet m d).biUnion (parameterResidueFiber R d) := by
  ext t
  rw [mem_divisibleParameterSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨htR, htDiv⟩
    let a : Fin d := ⟨t % d, Nat.mod_lt t hd⟩
    have hta : t ≡ a.val [MOD d] := (Nat.mod_modEq t d).symm
    have hvalue := shiftedProductValue_modEq (m := m) hta
    have haDiv : d ∣ shiftedProductValue m a.val :=
      Nat.modEq_zero_iff_dvd.mp (hvalue.symm.trans htDiv.modEq_zero_nat)
    exact ⟨a, by simpa using haDiv,
      mem_parameterResidueFiber.mpr ⟨htR, hta⟩⟩
  · rintro ⟨a, haRoot, hta⟩
    have htaData := mem_parameterResidueFiber.mp hta
    have haDiv : d ∣ shiftedProductValue m a := by simpa using haRoot
    have hvalue := shiftedProductValue_modEq (m := m) htaData.2
    exact ⟨htaData.1,
      Nat.modEq_zero_iff_dvd.mp (hvalue.trans haDiv.modEq_zero_nat)⟩

theorem parameterResidueFiber_pairwiseDisjoint (m R d : ℕ) :
    ((shiftedBadResidueSet m d : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint
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
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt,
    Nat.mod_eq_of_lt b.isLt] using habMod

/-- Exact count, with the final incomplete residue block retained.-/
theorem card_divisibleParameterSet_eq {m R d : ℕ} (hd : 0 < d) :
    (divisibleParameterSet m R d).card =
      shiftedBadResidueCount m d * (R / d) + residueExcessCount m R d := by
  rw [divisibleParameterSet_eq_biUnion hd,
    Finset.card_biUnion (parameterResidueFiber_pairwiseDisjoint m R d)]
  simp_rw [card_parameterResidueFiber hd]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const_nat, shiftedBadResidueCount,
    residueExcessCount, Finset.card_filter]

theorem card_divisibleParameterSet_cast_eq_main_add_error
    {m R d : ℕ} (hd : 0 < d) :
    ((divisibleParameterSet m R d).card : ℝ) =
      (shiftedBadResidueCount m d : ℝ) * (R / d : ℕ) +
        residueExcessCount m R d := by
  exact_mod_cast card_divisibleParameterSet_eq hd

theorem residueExcessCount_cast_le (m R d : ℕ) :
    (residueExcessCount m R d : ℝ) ≤ shiftedBadResidueCount m d := by
  exact_mod_cast residueExcessCount_le m R d

/-! ## The even-multiplier Selberg datum -/

/-- Local density of shifted-product roots modulo `p`.-/
def localDensity (m p : ℕ) : ℝ :=
  (shiftedBadResidueCount m p : ℝ) / p

/-- Multiplicative sieve density generated by the prime local densities.-/
def sieveDensity (m : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (localDensity m)

theorem sieveDensity_isMultiplicative (m : ℕ) :
    (sieveDensity m).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors (localDensity m)

@[simp]
theorem sieveDensity_apply_prime {m p : ℕ} (hp : p.Prime) :
    sieveDensity m p = localDensity m p := by
  rw [sieveDensity, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp.primeFactors]

/-- Product of every sifting prime at most `z`.-/
def primeProduct (z : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE z, p

theorem primeProduct_squarefree (z : ℕ) : Squarefree (primeProduct z) := by
  rw [primeProduct]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq ↦ ?_)
    (fun p hp ↦ (Nat.prime_of_mem_primesLE hp).squarefree)
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (Nat.prime_of_mem_primesLE hp)
    (Nat.prime_of_mem_primesLE hq)).mpr hpq

theorem prime_dvd_primeProduct_iff {z p : ℕ} (hp : p.Prime) :
    p ∣ primeProduct z ↔ p ∈ Nat.primesLE z := by
  constructor
  · intro hpd
    rw [primeProduct, hp.prime.dvd_finsetProd_iff] at hpd
    obtain ⟨q, hq, hpq⟩ := hpd
    have hqPrime := Nat.prime_of_mem_primesLE hq
    have hpqEq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq
    simpa [hpqEq] using hq
  · intro hpz
    exact dvd_prod_of_mem _ hpz

/-- Concrete Mathlib bounding sieve for an even multiplier.-/
def boundingSieve (m R z : ℕ) (hm : Even m) : BoundingSieve where
  support := selbergSupport m R
  prodPrimes := primeProduct z
  prodPrimes_squarefree := primeProduct_squarefree z
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ by norm_num
  totalMass := R
  nu := sieveDensity m
  nu_mult := sieveDensity_isMultiplicative m
  nu_pos_of_prime := by
    intro p hp _hpd
    rw [sieveDensity_apply_prime hp]
    unfold localDensity
    exact div_pos (by exact_mod_cast shiftedBadResidueCount_pos hp)
      (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpd
    rw [sieveDensity_apply_prime hp]
    unfold localDensity
    rw [div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast shiftedBadResidueCount_lt_prime_of_even hm hp

/-- Selberg-sieve structure attached to the shifted product support.-/
def selbergSieve (m R z : ℕ) (hm : Even m)
    (level : ℝ) (hlevel : 1 ≤ level) : SelbergSieve where
  toBoundingSieve := boundingSieve m R z hm
  level := level
  one_le_level := hlevel

theorem boundingSieve_multSum (m R z d : ℕ) (hm : Even m) :
    (boundingSieve m R z hm).multSum d =
      (divisibleParameterSet m R d).card := by
  simp [BoundingSieve.multSum, boundingSieve, selbergSupport,
    shiftedProductEmbedding, divisibleParameterSet]
  rw [Finset.filter_map, Finset.card_map]
  rfl

theorem boundingSieve_rem (m R z d : ℕ) (hm : Even m) :
    (boundingSieve m R z hm).rem d =
      (divisibleParameterSet m R d).card - sieveDensity m d * R := by
  rw [BoundingSieve.rem, boundingSieve_multSum]
  rfl

theorem boundingSieve_rem_eq_floor_add_excess
    {m R z d : ℕ} (hm : Even m) (hd : 0 < d) :
    (boundingSieve m R z hm).rem d =
      (shiftedBadResidueCount m d : ℝ) * (R / d : ℕ) +
        residueExcessCount m R d - sieveDensity m d * R := by
  rw [boundingSieve_rem, card_divisibleParameterSet_cast_eq_main_add_error hd]

theorem boundingSieve_rem_prime {m R z p : ℕ} (hm : Even m) (hp : p.Prime) :
    (boundingSieve m R z hm).rem p =
      (residueExcessCount m R p : ℝ) -
        (shiftedBadResidueCount m p : ℝ) * (R % p : ℕ) / p := by
  rw [boundingSieve_rem_eq_floor_add_excess hm hp.pos,
    sieveDensity_apply_prime hp]
  unfold localDensity
  have hR : (R : ℝ) = (p : ℝ) * (R / p : ℕ) + (R % p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div R p).symm.trans (by omega)
  rw [hR]
  have hpCast : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

theorem abs_boundingSieve_rem_prime_le
    {m R z p : ℕ} (hm : Even m) (hp : p.Prime) :
    |(boundingSieve m R z hm).rem p| ≤ shiftedBadResidueCount m p := by
  rw [boundingSieve_rem_prime hm hp]
  have hpCast : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hk0 : 0 ≤ (shiftedBadResidueCount m p : ℝ) := by positivity
  have he0 : 0 ≤ (residueExcessCount m R p : ℝ) := by positivity
  have hek : (residueExcessCount m R p : ℝ) ≤ shiftedBadResidueCount m p :=
    residueExcessCount_cast_le m R p
  have hfrac1 : ((R % p : ℕ) : ℝ) / p ≤ 1 := by
    rw [div_le_one hpCast]
    exact_mod_cast (Nat.mod_lt R hp.pos).le
  have hterm0 : 0 ≤
      (shiftedBadResidueCount m p : ℝ) * (R % p : ℕ) / p := by positivity
  have htermk :
      (shiftedBadResidueCount m p : ℝ) * (R % p : ℕ) / p ≤
        shiftedBadResidueCount m p := by
    calc
      (shiftedBadResidueCount m p : ℝ) * (R % p : ℕ) / p =
          (shiftedBadResidueCount m p : ℝ) * (((R % p : ℕ) : ℝ) / p) := by ring
      _ ≤ (shiftedBadResidueCount m p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfrac1 hk0
      _ = shiftedBadResidueCount m p := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ## Exact sifted-set identification -/

theorem coprime_primeProduct_iff {m z t : ℕ} :
    Nat.Coprime (primeProduct z) (shiftedProductValue m t) ↔
      ∀ p ∈ Nat.primesLE z, ¬p ∣ shiftedProductValue m t := by
  constructor
  · intro hcop p hpz
    have hp := Nat.prime_of_mem_primesLE hpz
    have hpcop : Nat.Coprime p (shiftedProductValue m t) := by
      rw [primeProduct, Nat.coprime_prod_left_iff] at hcop
      exact hcop p hpz
    exact hp.coprime_iff_not_dvd.mp hpcop
  · intro hall
    rw [primeProduct, Nat.coprime_prod_left_iff]
    intro p hpz
    exact (Nat.prime_of_mem_primesLE hpz).coprime_iff_not_dvd.mpr
      (hall p hpz)

/-- Parameters surviving all prime divisibility tests through `z`.-/
def siftedParameterSet (m R z : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t ↦
    Nat.Coprime (primeProduct z) (shiftedProductValue m t)

@[simp]
theorem mem_siftedParameterSet {m R z t : ℕ} :
    t ∈ siftedParameterSet m R z ↔
      t < R ∧ Nat.Coprime (primeProduct z) (shiftedProductValue m t) := by
  simp [siftedParameterSet]

/-- Paper-style sifted parameters `1 ≤ q ≤ R`.-/
def siftedPairSet (m R z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter fun q ↦
    ∀ p ∈ Nat.primesLE z, ¬p ∣ productValue m q

@[simp]
theorem mem_siftedPairSet {m R z q : ℕ} :
    q ∈ siftedPairSet m R z ↔
      1 ≤ q ∧ q ≤ R ∧ ∀ p ∈ Nat.primesLE z, ¬p ∣ productValue m q := by
  simp [siftedPairSet, and_assoc]

theorem siftedPairSet_eq_map (m R z : ℕ) :
    siftedPairSet m R z =
      (siftedParameterSet m R z).map AffinePrimePair.parameterShiftEmbedding := by
  ext q
  constructor
  · intro hq
    have hqData := mem_siftedPairSet.mp hq
    have hshift : q - 1 + 1 = q := by omega
    rw [Finset.mem_map]
    refine ⟨q - 1, ?_, ?_⟩
    · apply mem_siftedParameterSet.mpr
      refine ⟨by omega, ?_⟩
      rw [coprime_primeProduct_iff]
      simpa [shiftedProductValue, hshift] using hqData.2.2
    · simp only [AffinePrimePair.parameterShiftEmbedding_apply, hshift]
  · intro hq
    rw [Finset.mem_map] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have htData := mem_siftedParameterSet.mp ht
    apply mem_siftedPairSet.mpr
    refine ⟨by change 1 ≤ t + 1; omega, by change t + 1 ≤ R; omega, ?_⟩
    rw [coprime_primeProduct_iff] at htData
    simpa [AffinePrimePair.parameterShiftEmbedding_apply,
      shiftedProductValue] using htData.2

/-! ## From prime pairs to the sifted sum -/

theorem rightValue_strictMono {m : ℕ} (hm : 0 < m) :
    StrictMono fun q ↦ m * q + 1 := by
  intro q r hqr
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hqr hm) 1

/-- Prime pairs whose left affine value is at most the sieve cutoff.-/
def leftSmallPrimePairSet (m R z : ℕ) : Finset ℕ :=
  (bfpsAffinePrimeSet m 0 R).filter fun q ↦ q ≤ z

@[simp]
theorem mem_leftSmallPrimePairSet {m R z q : ℕ} :
    q ∈ leftSmallPrimePairSet m R z ↔
      q ∈ bfpsAffinePrimeSet m 0 R ∧ q ≤ z := by
  simp [leftSmallPrimePairSet]

/-- Prime pairs whose right affine value is at most the sieve cutoff.-/
def rightSmallPrimePairSet (m R z : ℕ) : Finset ℕ :=
  (bfpsAffinePrimeSet m 0 R).filter fun q ↦ m * q + 1 ≤ z

@[simp]
theorem mem_rightSmallPrimePairSet {m R z q : ℕ} :
    q ∈ rightSmallPrimePairSet m R z ↔
      q ∈ bfpsAffinePrimeSet m 0 R ∧ m * q + 1 ≤ z := by
  simp [rightSmallPrimePairSet]

theorem card_leftSmallPrimePairSet_le (m R z : ℕ) :
    (leftSmallPrimePairSet m R z).card ≤ z + 1 := by
  rw [← Finset.card_range (z + 1)]
  refine Finset.card_le_card_of_injOn id ?_ ?_
  · intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
      (mem_leftSmallPrimePairSet.mp hq).2)
  · intro q _hq r _hr hqr
    exact hqr

theorem card_rightSmallPrimePairSet_le
    {m : ℕ} (hm : 0 < m) (R z : ℕ) :
    (rightSmallPrimePairSet m R z).card ≤ z + 1 := by
  rw [← Finset.card_range (z + 1)]
  refine Finset.card_le_card_of_injOn (fun q ↦ m * q + 1) ?_ ?_
  · intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
      (mem_rightSmallPrimePairSet.mp hq).2)
  · intro q _hq r _hr hqr
    exact (rightValue_strictMono hm).injective hqr

theorem mem_siftedPairSet_of_prime_values_gt
    {m R z q : ℕ} (hq : q ∈ bfpsAffinePrimeSet m 0 R)
    (hqLarge : z < q) (hrightLarge : z < m * q + 1) :
    q ∈ siftedPairSet m R z := by
  have hqData := mem_bfpsAffinePrimeSet.mp hq
  apply mem_siftedPairSet.mpr
  refine ⟨by omega, hqData.2.1, ?_⟩
  intro p hpz hpd
  have hp : p.Prime := Nat.prime_of_mem_primesLE hpz
  have hple : p ≤ z := Nat.le_of_mem_primesLE hpz
  rcases hp.dvd_mul.mp hpd with hpLeft | hpRight
  · have heq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hqData.2.2.1).mp hpLeft
    omega
  · have heq : p = m * q + 1 :=
      (Nat.prime_dvd_prime_iff_eq hp hqData.2.2.2).mp hpRight
    omega

theorem primePairSet_subset_sifted_union_small
    (m R z : ℕ) :
    bfpsAffinePrimeSet m 0 R ⊆
      (siftedPairSet m R z ∪ leftSmallPrimePairSet m R z) ∪
        rightSmallPrimePairSet m R z := by
  intro q hq
  by_cases hleft : z < q
  · by_cases hright : z < m * q + 1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (mem_siftedPairSet_of_prime_values_gt hq hleft hright))))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_rightSmallPrimePairSet.mpr ⟨hq, Nat.le_of_not_gt hright⟩))
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
      (mem_leftSmallPrimePairSet.mpr ⟨hq, Nat.le_of_not_gt hleft⟩))))

theorem card_primePairSet_le_sifted_add
    {m : ℕ} (hm : 0 < m) (R z : ℕ) :
    (bfpsAffinePrimeSet m 0 R).card ≤
      (siftedPairSet m R z).card + 2 * (z + 1) := by
  calc
    (bfpsAffinePrimeSet m 0 R).card ≤
        ((siftedPairSet m R z ∪ leftSmallPrimePairSet m R z) ∪
          rightSmallPrimePairSet m R z).card :=
      Finset.card_le_card (primePairSet_subset_sifted_union_small m R z)
    _ ≤ (siftedPairSet m R z ∪ leftSmallPrimePairSet m R z).card +
        (rightSmallPrimePairSet m R z).card := Finset.card_union_le _ _
    _ ≤ ((siftedPairSet m R z).card + (leftSmallPrimePairSet m R z).card) +
        (rightSmallPrimePairSet m R z).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((siftedPairSet m R z).card + (z + 1)) + (z + 1) :=
      Nat.add_le_add
        (Nat.add_le_add_left (card_leftSmallPrimePairSet_le m R z) _)
        (card_rightSmallPrimePairSet_le hm R z)
    _ = (siftedPairSet m R z).card + 2 * (z + 1) := by omega

theorem bfpsAffinePrimeSet_subset_full (m lo hi : ℕ) :
    bfpsAffinePrimeSet m lo hi ⊆ bfpsAffinePrimeSet m 0 hi := by
  intro q hq
  have hqData := mem_bfpsAffinePrimeSet.mp hq
  exact mem_bfpsAffinePrimeSet.mpr
    ⟨by omega, hqData.2.1, hqData.2.2.1, hqData.2.2.2⟩

theorem card_bfpsAffinePrimeSet_le_full (m lo hi : ℕ) :
    (bfpsAffinePrimeSet m lo hi).card ≤ (bfpsAffinePrimeSet m 0 hi).card :=
  Finset.card_le_card (bfpsAffinePrimeSet_subset_full m lo hi)

/-! ## The odd-multiplier branch -/

theorem eq_two_of_mem_bfpsAffinePrimeSet_of_odd
    {m lo hi q : ℕ} (hm : 2 ≤ m) (hmOdd : Odd m)
    (hq : q ∈ bfpsAffinePrimeSet m lo hi) : q = 2 := by
  have hqData := mem_bfpsAffinePrimeSet.mp hq
  rcases hqData.2.2.1.eq_two_or_odd' with hqTwo | hqOdd
  · exact hqTwo
  · have hrightEven : Even (m * q + 1) := (hmOdd.mul hqOdd).add_one
    have hrightTwo : m * q + 1 = 2 := hqData.2.2.2.even_iff.mp hrightEven
    have hprodLower : 4 ≤ m * q :=
      Nat.mul_le_mul hm hqData.2.2.1.two_le
    omega

theorem card_bfpsAffinePrimeSet_le_one_of_odd
    {m : ℕ} (hm : 2 ≤ m) (hmOdd : Odd m) (lo hi : ℕ) :
    (bfpsAffinePrimeSet m lo hi).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  rw [eq_two_of_mem_bfpsAffinePrimeSet_of_odd hm hmOdd hq,
    eq_two_of_mem_bfpsAffinePrimeSet_of_odd hm hmOdd hr]

/-! ## Honest dimension-two and Mertens endpoints -/

/-- Euler product of local survival densities through `z`.-/
def localSieveProduct (m z : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE z, (1 - localDensity m p)

/-- Terminal finite-dimensional Selberg fundamental-lemma input, uniform in even `m`.-/
def SelbergFundamentalLemmaUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → ∀ hm : Even m, 3 ≤ R →
    (boundingSieve m R (cutoff R) hm).siftedSum ≤
      C * R * localSieveProduct m (cutoff R)

/-- Terminal Mertens/singular-factor estimate.-/
def MertensLocalProductUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → Even m → 3 ≤ R →
    localSieveProduct m (cutoff R) ≤
      C / (Real.log R) ^ 2 * ((m : ℝ) / (m.totient : ℝ))

/-- BFPS counterpart of `AffinePrimePair.DimensionTwoSelbergUpperBound`.-/
def DimensionTwoSelbergUpperBound
    (cutoff : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ m R, 2 ≤ m → ∀ hm : Even m, 3 ≤ R →
    (boundingSieve m R (cutoff R) hm).siftedSum ≤
      C * bfpsLogSquaredScale R * ((m : ℝ) / (m.totient : ℝ))

theorem dimensionTwoSelbergUpperBound_of_fundamental_and_mertens
    {cutoff : ℕ → ℕ} {Cfund Cmertens : ℝ} (hCfund : 0 ≤ Cfund)
    (hfund : SelbergFundamentalLemmaUpperBound cutoff Cfund)
    (hmertens : MertensLocalProductUpperBound cutoff Cmertens) :
    DimensionTwoSelbergUpperBound cutoff (Cfund * Cmertens) := by
  intro m R hm hmEven hR
  calc
    (boundingSieve m R (cutoff R) hmEven).siftedSum ≤
        Cfund * R * localSieveProduct m (cutoff R) :=
      hfund m R hm hmEven hR
    _ ≤ Cfund * R *
        (Cmertens / (Real.log R) ^ 2 * ((m : ℝ) / (m.totient : ℝ))) :=
      mul_le_mul_of_nonneg_left (hmertens m R hm hmEven hR)
        (mul_nonneg hCfund (by positivity))
    _ = (Cfund * Cmertens) * bfpsLogSquaredScale R *
        ((m : ℝ) / (m.totient : ℝ)) := by
      unfold bfpsLogSquaredScale AffinePrimePair.logSquaredScale
      ring

theorem one_le_bfpsTotientRatio {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) ≤ (m : ℝ) / (m.totient : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hm)]
  norm_num
  exact_mod_cast Nat.totient_le m

end BFPSTwoAffine

end

end RankAmplification
