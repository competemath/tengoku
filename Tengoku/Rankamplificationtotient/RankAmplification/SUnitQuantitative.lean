import Tengoku.Rankamplificationtotient.RankAmplification.SUnitTerminal
import Tengoku.Seed.NumberTheory.Height.NumberField
import Tengoku.Seed.NumberTheory.Height.MvPolynomial
import Tengoku.Seed.NumberTheory.Cyclotomic.PrimitiveRoots
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Embeddings
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.NumberTheory.Padics.PadicNorm
import Tengoku.Seed.NumberTheory.RamificationInertia.Basic
import Tengoku.Seed.Combinatorics.Enumerative.Composition
import Tengoku.Seed.LinearAlgebra.Vandermonde

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Quantitative rational S-unit equations This module develops the exact rational specialization used in Pollack--Pomerance--Treviño, Lemma 3.2. -/

namespace RankAmplification

open Finset Nat
open NumberField
open scoped BigOperators

noncomputable section

namespace SUnitQuantitative

/-! ## Rational S-units and the equation `x+y=1` -/

/-- A rational number represented, up to sign, by a quotient of positive natural `S`-units.-/
def IsRationalSUnit (S : Finset ℕ) (q : ℚ) : Prop :=
  ∃ a b : ℕ,
    IsPrimeSupportUnit S a ∧ IsPrimeSupportUnit S b ∧
      (q = (a : ℚ) / (b : ℚ) ∨ q = -((a : ℚ) / (b : ℚ)))

theorem IsRationalSUnit.ne_zero
    {S : Finset ℕ} {q : ℚ} (hq : IsRationalSUnit S q) : q ≠ 0 := by
  rintro rfl
  obtain ⟨a, b, ha, hb, hab | hab⟩ := hq
  · have haCast : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne_zero
    have hbCast : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne_zero
    exact haCast (div_eq_zero_iff.mp hab.symm |>.resolve_right hbCast)
  · have haCast : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne_zero
    have hbCast : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne_zero
    have hzero : (a : ℚ) / (b : ℚ) = 0 := by linarith
    exact haCast (div_eq_zero_iff.mp hzero |>.resolve_right hbCast)

theorem IsRationalSUnit.of_nat_div
    {S : Finset ℕ} {a b : ℕ}
    (ha : IsPrimeSupportUnit S a) (hb : IsPrimeSupportUnit S b) :
    IsRationalSUnit S ((a : ℚ) / (b : ℚ)) :=
  ⟨a, b, ha, hb, Or.inl rfl⟩

theorem IsRationalSUnit.neg_of_nat_div
    {S : Finset ℕ} {a b : ℕ}
    (ha : IsPrimeSupportUnit S a) (hb : IsPrimeSupportUnit S b) :
    IsRationalSUnit S (-((a : ℚ) / (b : ℚ))) :=
  ⟨a, b, ha, hb, Or.inr rfl⟩

theorem IsRationalSUnit.neg
    {S : Finset ℕ} {q : ℚ} (hq : IsRationalSUnit S q) :
    IsRationalSUnit S (-q) := by
  obtain ⟨a, b, ha, hb, hab | hab⟩ := hq
  · exact ⟨a, b, ha, hb, Or.inr (congrArg Neg.neg hab)⟩
  · refine ⟨a, b, ha, hb, Or.inl ?_⟩
    linarith

/-- A rational solution of `x+y=1` in `S`-units.-/
def IsRationalSUnitEquationSolution
    (S : Finset ℕ) (x y : ℚ) : Prop :=
  IsRationalSUnit S x ∧ IsRationalSUnit S y ∧ x + y = 1

/-- An exact finite carrier for all rational `S`-unit solutions of `x+y=1`.-/
def IsRationalSUnitEquationCarrier
    (S : Finset ℕ) (U : Finset (ℚ × ℚ)) : Prop :=
  ∀ x y, (x, y) ∈ U ↔ IsRationalSUnitEquationSolution S x y

/-- Evertse's explicit rational bound, with one archimedean place and `|S|` finite places.-/
def rationalSUnitEquationBound (S : Finset ℕ) : ℕ :=
  3 * 7 ^ (3 + 2 * S.card)

/-- The exact quantitative `x+y=1` theorem whose proof is Evertse's gap argument.-/
def QuantitativeRationalSUnitEquationTheorem : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    ∃ U : Finset (ℚ × ℚ),
      IsRationalSUnitEquationCarrier S U ∧
        U.card ≤ rationalSUnitEquationBound S

/-! ## The PPT specialization -/

/-- The rational solution attached to a same-support index.-/
def sameSupportRationalPair (h j : ℕ) : ℚ × ℚ :=
  (((j + h : ℕ) : ℚ) / (h : ℚ), -((j : ℚ) / (h : ℚ)))

theorem shift_isPrimeSupportUnit {h : ℕ} (hh : 0 < h) :
    IsPrimeSupportUnit (primeSupport h) h :=
  ⟨hh, fun _p hp ↦ hp⟩

theorem sameSupportRationalPair_isSolution
    {h j : ℕ} (hh : 0 < h) (hsame : IsSameSupportIndex h j) :
    IsRationalSUnitEquationSolution (primeSupport h)
      (sameSupportRationalPair h j).1 (sameSupportRationalPair h j).2 := by
  have hhUnit := shift_isPrimeSupportUnit hh
  refine ⟨IsRationalSUnit.of_nat_div
      (sameSupport_right_isPrimeSupportUnit hh hsame) hhUnit,
    IsRationalSUnit.neg_of_nat_div
      (sameSupport_left_isPrimeSupportUnit hh hsame) hhUnit, ?_⟩
  unfold sameSupportRationalPair
  simp only
  have hhCast : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp [hhCast]
  norm_cast
  omega

theorem sameSupportRationalPair_injective {h : ℕ} (hh : 0 < h) :
    Function.Injective (sameSupportRationalPair h) := by
  intro j k hjk
  have hsnd := congrArg Prod.snd hjk
  unfold sameSupportRationalPair at hsnd
  simp only at hsnd
  have hhCast : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp [hhCast] at hsnd
  norm_num at hsnd
  exact_mod_cast hsnd

/-- Recover the unique natural index represented by a rational pair, using zero off the image.-/
def rationalPairIndex (h : ℕ) (z : ℚ × ℚ) : ℕ :=
  by
    classical
    exact if hz : ∃ j, sameSupportRationalPair h j = z then Classical.choose hz else 0

theorem rationalPairIndex_sameSupportRationalPair
    {h j : ℕ} (hh : 0 < h) :
    rationalPairIndex h (sameSupportRationalPair h j) = j := by
  classical
  unfold rationalPairIndex
  split
  · rename_i hz
    exact sameSupportRationalPair_injective hh (Classical.choose_spec hz)
  · rename_i hz
    exact (hz ⟨j, rfl⟩).elim

/-- Pull a rational equation carrier back to an exact carrier of same-support indices.-/
def sameSupportCarrierFromRational
    (h : ℕ) (U : Finset (ℚ × ℚ)) : Finset ℕ :=
  by
    classical
    exact (U.image (rationalPairIndex h)).filter (IsSameSupportIndex h)

theorem isSameSupportCarrier_sameSupportCarrierFromRational
    {h : ℕ} (hh : 0 < h) {U : Finset (ℚ × ℚ)}
    (hU : IsRationalSUnitEquationCarrier (primeSupport h) U) :
    IsSameSupportCarrier h (sameSupportCarrierFromRational h U) := by
  classical
  intro j
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hsame
    rw [sameSupportCarrierFromRational, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨sameSupportRationalPair h j, ?_, ?_⟩, hsame⟩
    · exact (hU _ _).mpr (sameSupportRationalPair_isSolution hh hsame)
    · exact rationalPairIndex_sameSupportRationalPair hh

theorem card_sameSupportCarrierFromRational_le
    (h : ℕ) (U : Finset (ℚ × ℚ)) :
    (sameSupportCarrierFromRational h U).card ≤ U.card := by
  classical
  unfold sameSupportCarrierFromRational
  exact (Finset.card_filter_le _ _).trans Finset.card_image_le

theorem rationalSUnitEquationBound_primeSupport (h : ℕ) :
    rationalSUnitEquationBound (primeSupport h) = pptSameSupportBound h :=
  rfl

/-- The finite PPT conclusion follows formally from the quantitative rational unit-equation theorem.-/
theorem terminalPPTSameSupportBound_of_quantitativeRationalSUnitEquation
    {h : ℕ} (hh : 0 < h)
    (hE : QuantitativeRationalSUnitEquationTheorem) :
    TerminalPPTSameSupportBound h := by
  have hprime : ∀ p ∈ primeSupport h, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors hp
  obtain ⟨U, hU, hcard⟩ := hE (primeSupport h) hprime
  refine ⟨sameSupportCarrierFromRational h U,
    isSameSupportCarrier_sameSupportCarrierFromRational hh hU, ?_⟩
  exact (card_sameSupportCarrierFromRational_le h U).trans
    (by simpa [rationalSUnitEquationBound_primeSupport] using hcard)

/-! ## Finite-place valuation interface -/

/-- The additive `p`-adic order on rationals used in the finite-place part of Evertse's proof.-/
def rationalPrimeOrder (p : ℕ) (q : ℚ) : ℤ :=
  padicValRat p q

theorem rationalPrimeOrder_mul
    {p : ℕ} (hp : p.Prime) {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    rationalPrimeOrder p (q * r) =
      rationalPrimeOrder p q + rationalPrimeOrder p r := by
  letI : Fact p.Prime := ⟨hp⟩
  exact padicValRat.mul hq hr

theorem rationalPrimeOrder_neg (p : ℕ) (q : ℚ) :
    rationalPrimeOrder p (-q) = rationalPrimeOrder p q :=
  padicValRat.neg q

/-- The normalized finite absolute value attached to a rational prime.-/
def rationalPrimeNorm (p : ℕ) (q : ℚ) : ℚ :=
  padicNorm p q

theorem rationalPrimeNorm_mul
    {p : ℕ} (hp : p.Prime) (q r : ℚ) :
    rationalPrimeNorm p (q * r) =
      rationalPrimeNorm p q * rationalPrimeNorm p r := by
  letI : Fact p.Prime := ⟨hp⟩
  exact padicNorm.mul q r

theorem rationalPrimeNorm_div
    {p : ℕ} (hp : p.Prime) (q r : ℚ) :
    rationalPrimeNorm p (q / r) =
      rationalPrimeNorm p q / rationalPrimeNorm p r := by
  letI : Fact p.Prime := ⟨hp⟩
  exact padicNorm.div q r

theorem rationalPrimeNorm_neg (p : ℕ) (q : ℚ) :
    rationalPrimeNorm p (-q) = rationalPrimeNorm p q :=
  padicNorm.neg q

theorem rationalPrimeNorm_nonarchimedean
    {p : ℕ} (hp : p.Prime) (q r : ℚ) :
    rationalPrimeNorm p (q + r) ≤
      max (rationalPrimeNorm p q) (rationalPrimeNorm p r) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact padicNorm.nonarchimedean

theorem IsRationalSUnit.rationalPrimeOrder_eq_zero_of_not_mem
    {S : Finset ℕ} {q : ℚ} (hq : IsRationalSUnit S q)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    rationalPrimeOrder p q = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, ha, hb, hab | hab⟩ := hq
  all_goals
    have hpa : ¬p ∣ a := by
      intro hpa
      exact hpS (ha.2 (Nat.mem_primeFactors.mpr ⟨hp, hpa, ha.ne_zero⟩))
    have hpb : ¬p ∣ b := by
      intro hpb
      exact hpS (hb.2 (Nat.mem_primeFactors.mpr ⟨hp, hpb, hb.ne_zero⟩))
    have hva : padicValRat p (a : ℚ) = 0 := by
      simp only [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hpa
    have hvb : padicValRat p (b : ℚ) = 0 := by
      simp only [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hpb
    have haCast : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne_zero
    have hbCast : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne_zero
  · rw [hab, rationalPrimeOrder, padicValRat.div haCast hbCast, hva, hvb, sub_zero]
  · rw [hab, rationalPrimeOrder, padicValRat.neg,
      padicValRat.div haCast hbCast, hva, hvb, sub_zero]

theorem IsRationalSUnit.rationalPrimeNorm_eq_one_of_not_mem
    {S : Finset ℕ} {q : ℚ} (hq : IsRationalSUnit S q)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    rationalPrimeNorm p q = 1 := by
  have hv : padicValRat p q = 0 := by
    simpa only [rationalPrimeOrder] using
      hq.rationalPrimeOrder_eq_zero_of_not_mem hp hpS
  simp [rationalPrimeNorm, padicNorm, hq.ne_zero, hv]

/-! ## Native rational height -/

/-- The multiplicative Weil height on `ℚ`, exposed under a task-local name.-/
def rationalHeight (q : ℚ) : ℝ :=
  Height.mulHeight₁ q

/-- The logarithmic Weil height on `ℚ`.-/
def rationalLogHeight (q : ℚ) : ℝ :=
  Height.logHeight₁ q

theorem rationalHeight_eq_max_num_den (q : ℚ) :
    rationalHeight q = max q.num.natAbs q.den := by
  exact Rat.mulHeight₁_eq_max q

theorem rationalLogHeight_eq_log_max_num_den (q : ℚ) :
    rationalLogHeight q = Real.log ((max q.num.natAbs q.den : ℕ) : ℝ) := by
  simpa only [rationalLogHeight] using Rat.logHeight₁_eq_log_max q

theorem one_le_rationalHeight (q : ℚ) : 1 ≤ rationalHeight q :=
  Height.one_le_mulHeight₁ q

theorem zero_le_rationalLogHeight (q : ℚ) : 0 ≤ rationalLogHeight q :=
  Height.zero_le_logHeight₁ q

theorem rationalHeight_inv (q : ℚ) :
    rationalHeight q⁻¹ = rationalHeight q :=
  Height.mulHeight₁_inv q

theorem rationalHeight_neg (q : ℚ) :
    rationalHeight (-q) = rationalHeight q :=
  Height.mulHeight₁_neg q

theorem rationalHeight_pow (q : ℚ) (n : ℕ) :
    rationalHeight (q ^ n) = rationalHeight q ^ n :=
  Height.mulHeight₁_pow q n

theorem rationalHeight_mul_le (q r : ℚ) :
    rationalHeight (q * r) ≤ rationalHeight q * rationalHeight r :=
  Height.mulHeight₁_mul_le q r

theorem rationalLogHeight_pow (q : ℚ) (n : ℕ) :
    rationalLogHeight (q ^ n) = n * rationalLogHeight q :=
  Height.logHeight₁_pow q n

theorem rationalLogHeight_mul_le (q r : ℚ) :
    rationalLogHeight (q * r) ≤ rationalLogHeight q + rationalLogHeight r :=
  Height.logHeight₁_mul_le q r

/-- Northcott finiteness for the rational height; this is the finite-height input in the small-height branch of Evertse's proof.-/
theorem finite_rationalHeight_le (B : ℝ) :
    {q : ℚ | rationalHeight q ≤ B}.Finite :=
  NumberField.finite_setOfPred_mulHeight₁_le ℚ B

/-! ## Canonical exponent vectors -/

/-- Integer exponent vectors indexed by the supplied finite prime set.-/
abbrev RationalExponentVector (S : Finset ℕ) := S → ℤ

/-- The canonical exponent vector of a rational number, given by its finite-place orders.-/
def rationalExponentVector (S : Finset ℕ) (q : ℚ) : RationalExponentVector S :=
  fun p ↦ rationalPrimeOrder p q

/-- Evaluate an exponent vector as a rational Laurent monomial.-/
def rationalMonomial (S : Finset ℕ) (e : RationalExponentVector S) : ℚ :=
  ∏ p : S, (p.1 : ℚ) ^ (e p)

/-- A positive natural `S`-unit is exactly the product of its prime-factorization coordinates over `S`.-/
theorem IsPrimeSupportUnit.eq_prod_factorization
    {S : Finset ℕ} {n : ℕ} (hn : IsPrimeSupportUnit S n) :
    n = ∏ p ∈ S, p ^ n.factorization p := by
  calc
    n = n.factorization.prod (fun p e ↦ p ^ e) :=
      (Nat.prod_factorization_pow_eq_self hn.ne_zero).symm
    _ = ∏ p ∈ S, p ^ n.factorization p :=
      Finsupp.prod_of_support_subset n.factorization hn.2 (fun p e ↦ p ^ e)
        (by simp)

theorem IsPrimeSupportUnit.cast_eq_prod_factorization
    {S : Finset ℕ} {n : ℕ} (hn : IsPrimeSupportUnit S n) :
    (n : ℚ) = ∏ p : S, (p.1 : ℚ) ^ n.factorization p.1 := by
  calc
    (n : ℚ) = ((∏ p ∈ S, p ^ n.factorization p : ℕ) : ℚ) := by
      exact_mod_cast IsPrimeSupportUnit.eq_prod_factorization hn
    _ = ∏ p ∈ S, (p : ℚ) ^ n.factorization p := by push_cast; rfl
    _ = ∏ p : S, (p.1 : ℚ) ^ n.factorization p.1 := by
      change (∏ p ∈ S, (p : ℚ) ^ n.factorization p) =
        ∏ p ∈ S.attach, (p.1 : ℚ) ^ n.factorization p.1
      simpa using
        (Finset.prod_attach S (fun p ↦ (p : ℚ) ^ n.factorization p)).symm

/-- The canonical exponent vector reconstructs a positive quotient of natural `S`-units.-/
theorem rationalMonomial_exponentVector_nat_div
    {S : Finset ℕ} {a b : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    (ha : IsPrimeSupportUnit S a) (hb : IsPrimeSupportUnit S b) :
    rationalMonomial S (rationalExponentVector S ((a : ℚ) / (b : ℚ))) =
      (a : ℚ) / (b : ℚ) := by
  have haCast : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne_zero
  have hbCast : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne_zero
  have hexponent (p : S) :
      rationalExponentVector S ((a : ℚ) / (b : ℚ)) p =
        (a.factorization p.1 : ℤ) - b.factorization p.1 := by
    letI : Fact p.1.Prime := ⟨hS p.1 p.2⟩
    rw [rationalExponentVector, rationalPrimeOrder,
      padicValRat.div haCast hbCast, padicValRat.of_nat, padicValRat.of_nat,
      ← a.factorization_def (hS p.1 p.2),
      ← b.factorization_def (hS p.1 p.2)]
  simp only [rationalMonomial]
  calc
    (∏ p : S, (p.1 : ℚ) ^ rationalExponentVector S ((a : ℚ) / (b : ℚ)) p) =
        ∏ p : S, (p.1 : ℚ) ^ a.factorization p.1 /
          (p.1 : ℚ) ^ b.factorization p.1 := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [hexponent p, zpow_natCast_sub_natCast₀]
      exact_mod_cast (hS p.1 p.2).ne_zero
    _ = (a : ℚ) / (b : ℚ) := by
      rw [Finset.prod_div_distrib,
        ← IsPrimeSupportUnit.cast_eq_prod_factorization ha,
        ← IsPrimeSupportUnit.cast_eq_prod_factorization hb]

theorem rationalExponentVector_neg (S : Finset ℕ) (q : ℚ) :
    rationalExponentVector S (-q) = rationalExponentVector S q := by
  funext p
  exact rationalPrimeOrder_neg p.1 q

theorem rationalMonomial_exponentVector_neg (S : Finset ℕ) (q : ℚ) :
    rationalMonomial S (rationalExponentVector S (-q)) =
      rationalMonomial S (rationalExponentVector S q) := by
  rw [rationalExponentVector_neg]

/-- Reconstruction of a nonzero rational `S`-unit from its canonical exponent vector and one sign bit.-/
theorem IsRationalSUnit.exists_sign_mul_rationalMonomial
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℚ}
    (hq : IsRationalSUnit S q) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      q = ε * rationalMonomial S (rationalExponentVector S q) := by
  obtain ⟨a, b, ha, hb, hab | hab⟩ := hq
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_mul, hab]
    exact (rationalMonomial_exponentVector_nat_div hS ha hb).symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [hab, neg_one_mul]
    congr 1
    rw [rationalMonomial_exponentVector_neg]
    exact (rationalMonomial_exponentVector_nat_div hS ha hb).symm

/-! ## Residues modulo the 49th-power subgroup -/

/-- Exponent residue vectors modulo `49`.-/
abbrev ExponentResidue49 (S : Finset ℕ) := S → Fin 49

/-- The canonical least-nonnegative residue vector of an integer exponent vector.-/
def exponentResidue49 {S : Finset ℕ}
    (e : RationalExponentVector S) : ExponentResidue49 S :=
  fun p ↦ ⟨(e p).natMod 49, Int.natMod_lt (by norm_num)⟩

/-- The coordinatewise Euclidean quotient after division by `49`.-/
def exponentQuotient49 {S : Finset ℕ}
    (e : RationalExponentVector S) : RationalExponentVector S :=
  fun p ↦ e p / 49

theorem exponentResidue49_add_mul_quotient
    {S : Finset ℕ} (e : RationalExponentVector S) (p : S) :
    ((exponentResidue49 e p : Fin 49) : ℕ) +
        49 * exponentQuotient49 e p = e p := by
  change (((e p).natMod 49 : ℕ) : ℤ) + 49 * (e p / 49) = e p
  rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (49 : ℤ) ≠ 0))]
  exact Int.emod_add_mul_ediv _ _

theorem exponentResidue49_add_quotient_mul
    {S : Finset ℕ} (e : RationalExponentVector S) (p : S) :
    ((exponentResidue49 e p : Fin 49) : ℕ) +
        exponentQuotient49 e p * 49 = e p := by
  rw [mul_comm]
  exact exponentResidue49_add_mul_quotient e p

/-- Evaluate a residue vector using ordinary nonnegative powers.-/
def rationalResidueRepresentative49
    (S : Finset ℕ) (r : ExponentResidue49 S) : ℚ :=
  ∏ p : S, (p.1 : ℚ) ^ (r p : ℕ)

theorem rationalMonomial_eq_residue_mul_pow
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (e : RationalExponentVector S) :
    rationalMonomial S e =
      rationalResidueRepresentative49 S (exponentResidue49 e) *
        rationalMonomial S (exponentQuotient49 e) ^ 49 := by
  rw [rationalMonomial, rationalResidueRepresentative49, rationalMonomial,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  have hpCast : (p.1 : ℚ) ≠ 0 := by exact_mod_cast (hS p.1 p.2).ne_zero
  calc
    (p.1 : ℚ) ^ e p =
        (p.1 : ℚ) ^ (((exponentResidue49 e p : Fin 49) : ℕ) +
          exponentQuotient49 e p * 49 : ℤ) := by
      rw [exponentResidue49_add_quotient_mul]
    _ = (p.1 : ℚ) ^ (((exponentResidue49 e p : Fin 49) : ℕ) : ℤ) *
        (p.1 : ℚ) ^ (exponentQuotient49 e p * 49) := by
      rw [zpow_add₀ hpCast]
    _ = (p.1 : ℚ) ^ ((exponentResidue49 e p : Fin 49) : ℕ) *
        ((p.1 : ℚ) ^ exponentQuotient49 e p) ^ 49 := by
      rw [zpow_natCast, zpow_mul]
      rfl

/-- A sign bit together with a residue vector evaluates to a rational representative.-/
def signedResidueRepresentative49
    (S : Finset ℕ) (z : Bool × ExponentResidue49 S) : ℚ :=
  if z.1 then -rationalResidueRepresentative49 S z.2
  else rationalResidueRepresentative49 S z.2

/-- The canonical finite family of signed residue classes modulo rational 49th powers.-/
def signedResidueRepresentatives49 (S : Finset ℕ) : Finset ℚ := by
  classical
  exact Finset.univ.image (signedResidueRepresentative49 S)

theorem card_signedResidueRepresentatives49_le (S : Finset ℕ) :
    (signedResidueRepresentatives49 S).card ≤ 2 * 49 ^ S.card := by
  classical
  calc
    (signedResidueRepresentatives49 S).card ≤
        (Finset.univ : Finset (Bool × ExponentResidue49 S)).card := by
      exact Finset.card_image_le
    _ = 2 * 49 ^ S.card := by
      simp

/-- Every rational `S`-unit is represented by one of the signed residue vectors, modulo a 49th power.-/
theorem IsRationalSUnit.exists_mem_signedResidueRepresentatives49_mul_pow
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℚ}
    (hq : IsRationalSUnit S q) :
    ∃ r ∈ signedResidueRepresentatives49 S, ∃ z : ℚ, q = r * z ^ 49 := by
  classical
  obtain ⟨ε, hε, hqε⟩ := hq.exists_sign_mul_rationalMonomial hS
  let e := rationalExponentVector S q
  let rvec := exponentResidue49 e
  let z := rationalMonomial S (exponentQuotient49 e)
  have hsplit : rationalMonomial S e =
      rationalResidueRepresentative49 S rvec * z ^ 49 := by
    exact rationalMonomial_eq_residue_mul_pow hS e
  rcases hε with rfl | rfl
  · refine ⟨signedResidueRepresentative49 S (false, rvec), ?_, z, ?_⟩
    · exact Finset.mem_image.mpr ⟨(false, rvec), Finset.mem_univ _, rfl⟩
    · simpa [signedResidueRepresentative49, e, mul_assoc] using hqε.trans
        (congrArg (1 * ·) hsplit)
  · refine ⟨signedResidueRepresentative49 S (true, rvec), ?_, z, ?_⟩
    · exact Finset.mem_image.mpr ⟨(true, rvec), Finset.mem_univ _, rfl⟩
    · simpa [signedResidueRepresentative49, e, mul_assoc] using hqε.trans
        (congrArg ((-1 : ℚ) * ·) hsplit)

/-- Packaged finite-quotient statement: at most `2 * 49^|S|` classes cover all rational `S`-units modulo 49th powers.-/
theorem exists_signedResidueCarrier49
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ R : Finset ℚ, R.card ≤ 2 * 49 ^ S.card ∧
      ∀ q : ℚ, IsRationalSUnit S q →
        ∃ r ∈ R, ∃ z : ℚ, q = r * z ^ 49 :=
  ⟨signedResidueRepresentatives49 S,
    card_signedResidueRepresentatives49_le S,
    fun _q hq ↦ hq.exists_mem_signedResidueRepresentatives49_mul_pow hS⟩

/-! ## The low-height branch -/

theorem rationalHeight_div_le (q r : ℚ) :
    rationalHeight (q / r) ≤ rationalHeight q * rationalHeight r := by
  rw [div_eq_mul_inv]
  exact (rationalHeight_mul_le q r⁻¹).trans_eq
    (congrArg (rationalHeight q * ·) (rationalHeight_inv r))

theorem eq_one_or_neg_one_of_rationalHeight_lt_two
    {q : ℚ} (hq : q ≠ 0) (hheight : rationalHeight q < 2) :
    q = 1 ∨ q = -1 := by
  rw [rationalHeight_eq_max_num_den] at hheight
  have hmax : max q.num.natAbs q.den < 2 := by exact_mod_cast hheight
  have hden : q.den = 1 := by
    have hdenPos := q.den_pos
    have hdenLt : q.den < 2 := (le_max_right _ _).trans_lt hmax
    omega
  have hnumNe : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hnumPos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnumNe
  have hnumLt : q.num.natAbs < 2 := (le_max_left _ _).trans_lt hmax
  have hnumAbs : q.num.natAbs = 1 := by omega
  have hnum : q.num = 1 ∨ q.num = -1 := by
    omega
  rw [← Rat.coe_int_num_of_den_eq_one hden]
  rcases hnum with hnum | hnum
  · left
    simp [hnum]
  · right
    simp [hnum]

/-- A cutoff larger than Evertse's `exp 8`, chosen as a power of two so that two low-height elements in one 49th-power class have quotient of height strictly less than `2`.-/
def lowHeightCutoff49 : ℝ :=
  2 ^ 24

theorem lowHeightCutoff49_sq_lt_two_pow_49 :
    lowHeightCutoff49 * lowHeightCutoff49 < (2 : ℝ) ^ 49 := by
  norm_num [lowHeightCutoff49, ← pow_add]

theorem rationalHeight_ratio_lt_two_of_common_power49
    {r z₁ z₂ q₁ q₂ : ℚ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (h₁ : q₁ = r * z₁ ^ 49) (h₂ : q₂ = r * z₂ ^ 49)
    (hheight₁ : rationalHeight q₁ ≤ lowHeightCutoff49)
    (hheight₂ : rationalHeight q₂ ≤ lowHeightCutoff49) :
    rationalHeight (z₁ / z₂) < 2 := by
  have hr : r ≠ 0 := by
    intro hr
    exact hq₁ (by simp [h₁, hr])
  have hz₁ : z₁ ≠ 0 := by
    intro hz₁
    exact hq₁ (by simp [h₁, hz₁])
  have hz₂ : z₂ ≠ 0 := by
    intro hz₂
    exact hq₂ (by simp [h₂, hz₂])
  have hpow : (z₁ / z₂) ^ 49 = q₁ / q₂ := by
    rw [h₁, h₂, div_pow]
    field_simp
  have hheightPow : rationalHeight (z₁ / z₂) ^ 49 < (2 : ℝ) ^ 49 := by
    calc
      rationalHeight (z₁ / z₂) ^ 49 = rationalHeight ((z₁ / z₂) ^ 49) :=
        (rationalHeight_pow (z₁ / z₂) 49).symm
      _ = rationalHeight (q₁ / q₂) := by rw [hpow]
      _ ≤ rationalHeight q₁ * rationalHeight q₂ := rationalHeight_div_le q₁ q₂
      _ ≤ lowHeightCutoff49 * lowHeightCutoff49 :=
        mul_le_mul hheight₁ hheight₂
          (zero_le_one.trans (one_le_rationalHeight q₂))
          (by norm_num [lowHeightCutoff49])
      _ < (2 : ℝ) ^ 49 := lowHeightCutoff49_sq_lt_two_pow_49
  exact (pow_lt_pow_iff_left₀
    (zero_le_one.trans (one_le_rationalHeight (z₁ / z₂)))
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (49 : ℕ) ≠ 0)).mp hheightPow

theorem power49_class_pair_eq_or_eq_neg
    {r z₁ z₂ q₁ q₂ : ℚ}
    (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (h₁ : q₁ = r * z₁ ^ 49) (h₂ : q₂ = r * z₂ ^ 49)
    (hheight₁ : rationalHeight q₁ ≤ lowHeightCutoff49)
    (hheight₂ : rationalHeight q₂ ≤ lowHeightCutoff49) :
    q₁ = q₂ ∨ q₁ = -q₂ := by
  have hz₂ : z₂ ≠ 0 := by
    intro hz₂
    exact hq₂ (by simp [h₂, hz₂])
  rcases eq_one_or_neg_one_of_rationalHeight_lt_two
      (div_ne_zero (by
        intro hz₁
        exact hq₁ (by simp [h₁, hz₁])) hz₂)
      (rationalHeight_ratio_lt_two_of_common_power49 hq₁ hq₂ h₁ h₂
        hheight₁ hheight₂) with hratio | hratio
  · left
    have hz : z₁ = z₂ := (div_eq_one_iff_eq hz₂).mp hratio
    subst z₁
    exact h₁.trans h₂.symm
  · right
    have hz : z₁ = -z₂ := by
      have hzMul := (div_eq_iff hz₂).mp hratio
      simpa using hzMul
    rw [h₁, h₂, hz]
    ring

/-- The finite rational height ball at the low-height cutoff.-/
def rationalLowHeightBall49 : Finset ℚ :=
  (finite_rationalHeight_le lowHeightCutoff49).toFinset

@[simp]
theorem mem_rationalLowHeightBall49 {q : ℚ} :
    q ∈ rationalLowHeightBall49 ↔ rationalHeight q ≤ lowHeightCutoff49 := by
  simp [rationalLowHeightBall49]

/-- The nonzero members of one 49th-power class below the low-height cutoff.-/
def lowPowerClass49 (r : ℚ) : Finset ℚ := by
  classical
  exact rationalLowHeightBall49.filter fun q ↦
    q ≠ 0 ∧ ∃ z : ℚ, q = r * z ^ 49

@[simp]
theorem mem_lowPowerClass49 {r q : ℚ} :
    q ∈ lowPowerClass49 r ↔
      rationalHeight q ≤ lowHeightCutoff49 ∧ q ≠ 0 ∧
        ∃ z : ℚ, q = r * z ^ 49 := by
  classical
  simp [lowPowerClass49]

/-- Uniform two-element bound for a fixed signed 49th-power residue class.-/
theorem card_lowPowerClass49_le_two (r : ℚ) :
    (lowPowerClass49 r).card ≤ 2 := by
  classical
  by_cases hempty : lowPowerClass49 r = ∅
  · simp [hempty]
  · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    apply (Finset.card_le_card (t := {q₀, -q₀}) ?_).trans Finset.card_le_two
    intro q hq
    rw [Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨hqHeight, hqNe, z, hz⟩ := mem_lowPowerClass49.mp hq
    obtain ⟨hq₀Height, hq₀Ne, z₀, hz₀⟩ := mem_lowPowerClass49.mp hq₀
    exact power49_class_pair_eq_or_eq_neg hqNe hq₀Ne hz hz₀ hqHeight hq₀Height

/-- Union of all low-height classes represented by the canonical signed residue carrier.-/
def lowPowerClassUnion49 (S : Finset ℕ) : Finset ℚ := by
  classical
  exact (signedResidueRepresentatives49 S).biUnion lowPowerClass49

theorem card_lowPowerClassUnion49_le (S : Finset ℕ) :
    (lowPowerClassUnion49 S).card ≤ 4 * 49 ^ S.card := by
  classical
  calc
    (lowPowerClassUnion49 S).card ≤
        (signedResidueRepresentatives49 S).card * 2 := by
      exact Finset.card_biUnion_le_card_mul _ _ 2
        (fun r _hr ↦ card_lowPowerClass49_le_two r)
    _ ≤ (2 * 49 ^ S.card) * 2 :=
      Nat.mul_le_mul_right 2 (card_signedResidueRepresentatives49_le S)
    _ = 4 * 49 ^ S.card := by ring

theorem IsRationalSUnit.mem_lowPowerClassUnion49
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℚ}
    (hq : IsRationalSUnit S q)
    (hheight : rationalHeight q ≤ lowHeightCutoff49) :
    q ∈ lowPowerClassUnion49 S := by
  classical
  obtain ⟨r, hr, z, hz⟩ :=
    hq.exists_mem_signedResidueRepresentatives49_mul_pow hS
  exact Finset.mem_biUnion.mpr ⟨r, hr,
    mem_lowPowerClass49.mpr ⟨hheight, hq.ne_zero, z, hz⟩⟩

theorem IsRationalSUnit.inv
    {S : Finset ℕ} {q : ℚ} (hq : IsRationalSUnit S q) :
    IsRationalSUnit S q⁻¹ := by
  obtain ⟨a, b, ha, hb, hab | hab⟩ := hq
  · refine ⟨b, a, hb, ha, Or.inl ?_⟩
    rw [hab]
    field_simp
  · refine ⟨b, a, hb, ha, Or.inr ?_⟩
    rw [hab]
    field_simp

theorem IsRationalSUnit.mul
    {S : Finset ℕ} {q r : ℚ}
    (hq : IsRationalSUnit S q) (hr : IsRationalSUnit S r) :
    IsRationalSUnit S (q * r) := by
  obtain ⟨a, b, ha, hb, hq⟩ := hq
  obtain ⟨c, d, hc, hd, hr⟩ := hr
  have hac : IsPrimeSupportUnit S (a * c) :=
    SUnitTerminal.IsPrimeSupportUnit.mul ha hc
  have hbd : IsPrimeSupportUnit S (b * d) :=
    SUnitTerminal.IsPrimeSupportUnit.mul hb hd
  rcases hq with hq | hq <;> rcases hr with hr | hr
  · refine ⟨a * c, b * d, hac, hbd, Or.inl ?_⟩
    rw [hq, hr]
    push_cast
    ring
  · refine ⟨a * c, b * d, hac, hbd, Or.inr ?_⟩
    rw [hq, hr]
    push_cast
    ring
  · refine ⟨a * c, b * d, hac, hbd, Or.inr ?_⟩
    rw [hq, hr]
    push_cast
    ring
  · refine ⟨a * c, b * d, hac, hbd, Or.inl ?_⟩
    rw [hq, hr]
    push_cast
    ring

theorem IsRationalSUnit.div
    {S : Finset ℕ} {q r : ℚ}
    (hq : IsRationalSUnit S q) (hr : IsRationalSUnit S r) :
    IsRationalSUnit S (q / r) := by
  rw [div_eq_mul_inv]
  exact hq.mul hr.inv

/-- Recover a solution pair from its ratio.-/
def rationalEquationPairOfRatio (q : ℚ) : ℚ × ℚ :=
  (q / (q + 1), 1 / (q + 1))

theorem rationalEquationPairOfRatio_ratio_of_ne
    {q : ℚ} (hq : q + 1 ≠ 0) :
    (rationalEquationPairOfRatio q).1 /
        (rationalEquationPairOfRatio q).2 = q := by
  simp only [rationalEquationPairOfRatio]
  field_simp

theorem rationalEquationPairOfRatio_eq_of_solution
    {S : Finset ℕ} {x y : ℚ}
    (hsol : IsRationalSUnitEquationSolution S x y) :
    rationalEquationPairOfRatio (x / y) = (x, y) := by
  have hy : y ≠ 0 := hsol.2.1.ne_zero
  have hratioAdd : x / y + 1 = 1 / y := by
    field_simp
    linarith [hsol.2.2]
  ext <;> simp [rationalEquationPairOfRatio, hratioAdd, hy]

/-- The exact finite ratio set for low-height rational S-unit equation solutions.-/
def lowHeightRationalSUnitEquationRatioSet (S : Finset ℕ) : Finset ℚ := by
  classical
  exact (lowPowerClassUnion49 S).filter fun q ↦
    IsRationalSUnitEquationSolution S
      (rationalEquationPairOfRatio q).1 (rationalEquationPairOfRatio q).2

theorem card_lowHeightRationalSUnitEquationRatioSet_le (S : Finset ℕ) :
    (lowHeightRationalSUnitEquationRatioSet S).card ≤ 4 * 49 ^ S.card :=
  by
    classical
    exact (Finset.card_filter_le _ _).trans (card_lowPowerClassUnion49_le S)

/-- Exact finite carrier for low-height equation solutions, obtained from their ratios.-/
def lowHeightRationalSUnitEquationCarrier (S : Finset ℕ) : Finset (ℚ × ℚ) := by
  classical
  exact (lowHeightRationalSUnitEquationRatioSet S).image rationalEquationPairOfRatio

/-- Predicate for the low-height branch of the rational S-unit equation.-/
def IsLowHeightRationalSUnitEquationSolution
    (S : Finset ℕ) (x y : ℚ) : Prop :=
  IsRationalSUnitEquationSolution S x y ∧
    rationalHeight (x / y) ≤ lowHeightCutoff49

theorem height_le_of_mem_lowPowerClassUnion49
    {S : Finset ℕ} {q : ℚ} (hq : q ∈ lowPowerClassUnion49 S) :
    rationalHeight q ≤ lowHeightCutoff49 := by
  classical
  obtain ⟨r, _hr, hqr⟩ := Finset.mem_biUnion.mp hq
  exact (mem_lowPowerClass49.mp hqr).1

@[simp]
theorem mem_lowHeightRationalSUnitEquationRatioSet
    {S : Finset ℕ} {q : ℚ} :
    q ∈ lowHeightRationalSUnitEquationRatioSet S ↔
      q ∈ lowPowerClassUnion49 S ∧
        IsRationalSUnitEquationSolution S
          (rationalEquationPairOfRatio q).1
          (rationalEquationPairOfRatio q).2 := by
  classical
  simp [lowHeightRationalSUnitEquationRatioSet]

/-- Exact membership theorem for the constructed low-height solution carrier.-/
theorem mem_lowHeightRationalSUnitEquationCarrier
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {x y : ℚ} :
    (x, y) ∈ lowHeightRationalSUnitEquationCarrier S ↔
      IsLowHeightRationalSUnitEquationSolution S x y := by
  classical
  constructor
  · intro hxy
    obtain ⟨q, hq, hpair⟩ := Finset.mem_image.mp hxy
    have hqData := mem_lowHeightRationalSUnitEquationRatioSet.mp hq
    have hsol := hqData.2
    have hqAdd : q + 1 ≠ 0 := by
      intro hzero
      exact hsol.2.1.ne_zero (by
        simp [rationalEquationPairOfRatio, hzero])
    have hratio := rationalEquationPairOfRatio_ratio_of_ne hqAdd
    have hlow : IsLowHeightRationalSUnitEquationSolution S
        (rationalEquationPairOfRatio q).1 (rationalEquationPairOfRatio q).2 := ⟨hsol, by
      rw [hratio]
      exact height_le_of_mem_lowPowerClassUnion49 hqData.1⟩
    simpa only [hpair] using hlow
  · rintro ⟨hsol, hheight⟩
    let q := x / y
    have hqUnit : IsRationalSUnit S q := hsol.1.div hsol.2.1
    have hqUnion : q ∈ lowPowerClassUnion49 S :=
      hqUnit.mem_lowPowerClassUnion49 hS hheight
    have hpair : rationalEquationPairOfRatio q = (x, y) :=
      rationalEquationPairOfRatio_eq_of_solution hsol
    apply Finset.mem_image.mpr
    refine ⟨q, mem_lowHeightRationalSUnitEquationRatioSet.mpr ⟨hqUnion, ?_⟩, hpair⟩
    simpa only [hpair] using hsol

theorem card_lowHeightRationalSUnitEquationCarrier_le (S : Finset ℕ) :
    (lowHeightRationalSUnitEquationCarrier S).card ≤ 4 * 49 ^ S.card := by
  classical
  exact Finset.card_image_le.trans (card_lowHeightRationalSUnitEquationRatioSet_le S)

/-- Fully unconditional quantitative low-height branch of Evertse's rational theorem.-/
theorem exists_lowHeightRationalSUnitEquationCarrier
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ U : Finset (ℚ × ℚ),
      (∀ x y, (x, y) ∈ U ↔
        IsLowHeightRationalSUnitEquationSolution S x y) ∧
      U.card ≤ 4 * 49 ^ S.card :=
  ⟨lowHeightRationalSUnitEquationCarrier S,
    fun _x _y ↦ mem_lowHeightRationalSUnitEquationCarrier hS,
    card_lowHeightRationalSUnitEquationCarrier_le S⟩

/-! ## The cubic transform for the high-height branch -/

/-- Evertse's quadratic cyclotomic extension `ℚ(ρ)`, where `ρ` is a primitive cube root of unity.-/
abbrev EvertseCubicField := CyclotomicField 3 ℚ

local instance evertseThreeNeZero : NeZero (3 : ℚ) := ⟨by norm_num⟩

local instance evertseIsCyclotomic :
    IsCyclotomicExtension {3} ℚ EvertseCubicField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

/-- The selected primitive cube root in `ℚ(ρ)`.-/
def evertseRho : EvertseCubicField :=
  IsCyclotomicExtension.zeta 3 ℚ EvertseCubicField

theorem evertseRho_isPrimitiveRoot : IsPrimitiveRoot evertseRho 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ EvertseCubicField

/-- The two conjugate linear forms in Evertse's cubic transform.-/
def evertseXi (x y : ℚ) : EvertseCubicField :=
  algebraMap ℚ EvertseCubicField x -
    evertseRho * algebraMap ℚ EvertseCubicField y

def evertseEta (x y : ℚ) : EvertseCubicField :=
  algebraMap ℚ EvertseCubicField x -
    evertseRho ^ 2 * algebraMap ℚ EvertseCubicField y

theorem rational_quadratic_form_ne_zero_of_add_eq_one
    {x y : ℚ} (hxy : x + y = 1) :
    x ^ 2 + x * y + y ^ 2 ≠ 0 := by
  intro hzero
  nlinarith [sq_nonneg (x - y)]

/-- Evertse's projective cubic-transform coordinate `ζ = ξ/η`.-/
def evertseZeta (x y : ℚ) : EvertseCubicField :=
  evertseXi x y / evertseEta x y

/-- The coefficient matrix of the inverse Möbius transformation `ζ ↦ (ζρ²-ρ)/(ζ-1)`.-/
def evertseMobiusMatrix : Fin 2 × Fin 2 → EvertseCubicField :=
  fun ji ↦ ![![evertseRho ^ 2, -evertseRho], ![1, -1]] ji.1 ji.2

/-- The two-coordinate vector whose quotient is the inverse Möbius transformation.-/
def evertseMobiusVector (z : EvertseCubicField) : Fin 2 → EvertseCubicField :=
  ![z, 1]

/-- The normalized absolute height on the quadratic cyclotomic field.-/
def evertseNormalizedHeight (z : EvertseCubicField) : ℝ :=
  Real.sqrt (Height.mulHeight₁ z)

/-! ## Exact local identities -/

/-! ## The finite places over the rational support -/

/-- The prime ideal of `𝓞 ℚ` corresponding to a rational prime `p`.-/
def evertseRationalPrimeIdeal (p : ℕ) : Ideal (𝓞 ℚ) :=
  Ideal.map Rat.ringOfIntegersEquiv.symm (Ideal.span {(p : ℤ)})

theorem evertseRationalPrimeIdeal_ne_bot {p : ℕ} (hp : p.Prime) :
    evertseRationalPrimeIdeal p ≠ ⊥ := by
  intro hbot
  have hspan : Ideal.span {(p : ℤ)} = ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective Rat.ringOfIntegersEquiv.symm.injective).mp hbot
  rw [Ideal.span_singleton_eq_bot] at hspan
  exact hp.ne_zero (by exact_mod_cast hspan)

theorem evertseRationalPrimeIdeal_isPrime {p : ℕ} (hp : p.Prime) :
    (evertseRationalPrimeIdeal p).IsPrime := by
  letI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime]
    · exact Nat.prime_iff_prime_int.mp hp
    · exact_mod_cast hp.ne_zero
  exact Ideal.map_isPrime_of_equiv Rat.ringOfIntegersEquiv.symm

/-- Turn a prime ideal above `p` into the corresponding height-one point.-/
noncomputable def evertsePrimeIdealHeightOne
    (p : ℕ) (hp : p.Prime)
    (P : {P : Ideal (𝓞 EvertseCubicField) //
      P ∈ IsDedekindDomain.primesOverFinset (evertseRationalPrimeIdeal p)
        (𝓞 EvertseCubicField)}) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 EvertseCubicField) := by
  letI : (evertseRationalPrimeIdeal p).IsMaximal :=
    (evertseRationalPrimeIdeal_isPrime hp).isMaximal
      (evertseRationalPrimeIdeal_ne_bot hp)
  have hPover : P.1 ∈ (evertseRationalPrimeIdeal p).primesOver
      (𝓞 EvertseCubicField) :=
    (IsDedekindDomain.mem_primesOverFinset_iff
      (evertseRationalPrimeIdeal_ne_bot hp) _).mp P.2
  exact ⟨P.1, hPover.1,
    Ideal.ne_bot_of_mem_primesOver (evertseRationalPrimeIdeal_ne_bot hp) hPover⟩

/-- The finite set of finite places of `ℚ(ρ)` lying above a rational prime `p`.-/
noncomputable def evertseFinitePlacesAbovePrime
    (p : ℕ) (hp : p.Prime) : Finset (NumberField.FinitePlace EvertseCubicField) := by
  letI : (evertseRationalPrimeIdeal p).IsMaximal :=
    (evertseRationalPrimeIdeal_isPrime hp).isMaximal
      (evertseRationalPrimeIdeal_ne_bot hp)
  exact (IsDedekindDomain.primesOverFinset (evertseRationalPrimeIdeal p)
      (𝓞 EvertseCubicField)).attach.map
    ⟨fun P => NumberField.FinitePlace.mk (evertsePrimeIdealHeightOne p hp P), by
      intro P Q hPQ
      apply Subtype.ext
      have hspec : evertsePrimeIdealHeightOne p hp P =
          evertsePrimeIdealHeightOne p hp Q :=
        NumberField.FinitePlace.mk_eq_iff.mp hPQ
      exact IsDedekindDomain.HeightOneSpectrum.ext_iff.mp hspec⟩

/-- All finite places above a finite rational prime support.-/
noncomputable def evertseFinitePlacesOverSupport
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Finset (NumberField.FinitePlace EvertseCubicField) := by
  classical
  exact S.attach.biUnion fun p =>
    evertseFinitePlacesAbovePrime p.1 (hS p.1 p.2)

/-- The algebraic integer in `ℚ(ρ)` represented by a rational prime.-/
def evertsePrimeInteger (p : ℕ) : 𝓞 EvertseCubicField :=
  algebraMap (𝓞 ℚ) (𝓞 EvertseCubicField)
    (Rat.ringOfIntegersEquiv.symm (p : ℤ))

/-! ## The archimedean place and the ramified place above three -/

/-- The rational prime ideal `(3)` used for the unique ramified finite place.-/
def evertseThreePrimeIdeal : Ideal ℤ := Ideal.span {(3 : ℤ)}

theorem evertseThreePrimeIdeal_ne_bot : evertseThreePrimeIdeal ≠ ⊥ := by
  rw [evertseThreePrimeIdeal, ne_eq, Ideal.span_singleton_eq_bot]
  norm_num

theorem evertseThreePrimeIdeal_isPrime : evertseThreePrimeIdeal.IsPrime := by
  rw [evertseThreePrimeIdeal, Ideal.span_singleton_prime]
  · exact Nat.prime_iff_prime_int.mp (by decide)
  · norm_num

/-- Convert a prime above `(3)` into a height-one point of the cyclotomic ring of integers.-/
noncomputable def evertseThreePrimeIdealHeightOne
    (P : {P : Ideal (𝓞 EvertseCubicField) //
      P ∈ IsDedekindDomain.primesOverFinset evertseThreePrimeIdeal
        (𝓞 EvertseCubicField)}) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 EvertseCubicField) := by
  letI : evertseThreePrimeIdeal.IsMaximal :=
    evertseThreePrimeIdeal_isPrime.isMaximal evertseThreePrimeIdeal_ne_bot
  have hPover : P.1 ∈ evertseThreePrimeIdeal.primesOver
      (𝓞 EvertseCubicField) :=
    (IsDedekindDomain.mem_primesOverFinset_iff
      evertseThreePrimeIdeal_ne_bot _).mp P.2
  exact ⟨P.1, hPover.1,
    Ideal.ne_bot_of_mem_primesOver evertseThreePrimeIdeal_ne_bot hPover⟩

/-- The unique finite place of `ℚ(ρ)` above `3`.-/
noncomputable def evertseFinitePlacesAboveThree :
    Finset (NumberField.FinitePlace EvertseCubicField) := by
  letI : evertseThreePrimeIdeal.IsMaximal :=
    evertseThreePrimeIdeal_isPrime.isMaximal evertseThreePrimeIdeal_ne_bot
  exact (IsDedekindDomain.primesOverFinset evertseThreePrimeIdeal
      (𝓞 EvertseCubicField)).attach.map
    ⟨fun P => NumberField.FinitePlace.mk (evertseThreePrimeIdealHeightOne P), by
      intro P Q hPQ
      apply Subtype.ext
      have hspec : evertseThreePrimeIdealHeightOne P =
          evertseThreePrimeIdealHeightOne Q :=
        NumberField.FinitePlace.mk_eq_iff.mp hPQ
      exact IsDedekindDomain.HeightOneSpectrum.ext_iff.mp hspec⟩

/-- The finite places needed in Evertse's local system: those over `S` and the ramified place over `3`.-/
def evertseExceptionalFinitePlaces
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Finset (NumberField.FinitePlace EvertseCubicField) := by
  classical
  exact evertseFinitePlacesOverSupport S hS ∪ evertseFinitePlacesAboveThree

/-- The finite type of all local places retained in the high-height argument.-/
abbrev EvertsePlace (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :=
  Sum (NumberField.InfinitePlace EvertseCubicField)
    {w : NumberField.FinitePlace EvertseCubicField //
      w ∈ evertseExceptionalFinitePlaces S hS}

/-- The absolute value represented by a retained local place.-/
def evertsePlaceAbv
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime} :
    EvertsePlace S hS → AbsoluteValue EvertseCubicField ℝ
  | Sum.inl w => w.1
  | Sum.inr w => w.1.1

@[simp]
theorem evertsePlaceAbv_infinite
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (w : NumberField.InfinitePlace EvertseCubicField) :
    evertsePlaceAbv (S := S) (hS := hS) (Sum.inl w) = w.1 :=
  rfl

@[simp]
theorem evertsePlaceAbv_finite
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (w : {w : NumberField.FinitePlace EvertseCubicField //
      w ∈ evertseExceptionalFinitePlaces S hS}) :
    evertsePlaceAbv (S := S) (hS := hS) (Sum.inr w) = w.1.1 :=
  rfl

/-- The integral representative of the chosen cube root of unity.-/
def evertseRhoInteger : 𝓞 EvertseCubicField :=
  evertseRho_isPrimitiveRoot.toInteger

/-! ## Omitted-place local estimates -/

/-- Truncated local distance to one of the three cube roots of unity.-/
def evertseLocalCloseness
    (v : AbsoluteValue EvertseCubicField ℝ)
    (z root : EvertseCubicField) : ℝ :=
  min 1 (v (z - root))

/-! ## Product formula and the normalized three-root bound -/

lemma min_one_eq_div_max_one {a : ℝ} (ha : 0 < a) :
    min 1 a = a / max a 1 := by
  apply (eq_div_iff (lt_of_lt_of_le ha (le_max_left a 1)).ne').2
  rw [max_comm]
  simpa only [one_mul] using min_mul_max (1 : ℝ) a

/-- The product over all places of the truncated small part of a field element.-/
def evertseGlobalClosenessProduct (z : EvertseCubicField) : ℝ :=
  (∏ w : NumberField.InfinitePlace EvertseCubicField,
      (min 1 (w z)) ^ w.mult) *
    ∏ᶠ w : NumberField.FinitePlace EvertseCubicField, min 1 (w z)

/-- Square-root normalization of the global small-part product.-/
def evertseNormalizedGlobalClosenessProduct (z : EvertseCubicField) : ℝ :=
  Real.sqrt (evertseGlobalClosenessProduct z)

/-! ## Restricting the product to the finite Evertse place system -/

/-- The normalized retained product: ordinary local factors at the unique complex place and square roots of the finite-place factors.-/
def evertseRetainedNormalizedClosenessProduct
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (z root : EvertseCubicField) : ℝ :=
  (∏ w : NumberField.InfinitePlace EvertseCubicField,
      min 1 (w (z - root))) *
    ∏ w ∈ evertseExceptionalFinitePlaces S hS,
      Real.sqrt (min 1 (w (z - root)))

/-! ## The finite simplex of local exponent systems -/

/-- A weak composition of `q`, represented by `q` coordinates bounded by `q`.-/
def EvertseGammaIndex (q : ℕ) :=
  { k : Fin q → Fin (q + 1) // ∑ i, (k i : ℕ) = q }

instance (q : ℕ) : Fintype (EvertseGammaIndex q) := by
  unfold EvertseGammaIndex
  infer_instance

instance (q : ℕ) : DecidableEq (EvertseGammaIndex q) := by
  unfold EvertseGammaIndex
  infer_instance

namespace EvertseGammaIndex

/-- Add one to every coordinate of a weak composition of `q`, obtaining an ordinary composition of `2q` into `q` positive blocks.-/
def toComposition {q : ℕ} (k : EvertseGammaIndex q) : Composition (2 * q) where
  blocks := List.ofFn (fun i => (k.1 i : ℕ) + 1)
  blocks_pos := by
    simp only [List.mem_ofFn, forall_exists_index]
    intro i _hi
    omega
  blocks_sum := by
    rw [List.sum_ofFn, Finset.sum_add_distrib, k.2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    change q + q = 2 * q
    omega

@[simp]
theorem toComposition_blocks {q : ℕ} (k : EvertseGammaIndex q) :
    k.toComposition.blocks = List.ofFn (fun i => (k.1 i : ℕ) + 1) :=
  rfl

/-- The positive-block encoding of weak compositions is injective.-/
theorem toComposition_injective (q : ℕ) :
    Function.Injective (@toComposition q) := by
  intro k l h
  apply Subtype.ext
  have hb := congrArg Composition.blocks h
  have hf := List.ofFn_injective hb
  funext i
  apply Fin.ext
  have hi := congrFun hf i
  simpa using Nat.add_right_cancel hi

/-- The number of weak compositions of `q` is bounded by the number of all compositions of `2q`.-/
theorem card_le_compositions (q : ℕ) :
    Fintype.card (EvertseGammaIndex q) ≤ 2 ^ (2 * q - 1) := by
  rw [← composition_card (2 * q)]
  exact Fintype.card_le_of_injective _ (toComposition_injective q)

/-- A coarse exponential bound tailored to the constant in Evertse's theorem.-/
theorem card_le_seven_pow (q : ℕ) :
    Fintype.card (EvertseGammaIndex q) ≤ 7 ^ (q + 1) := by
  calc
    Fintype.card (EvertseGammaIndex q) ≤ 2 ^ (2 * q - 1) :=
      card_le_compositions q
    _ ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    _ = 4 ^ q := by rw [pow_mul]; norm_num
    _ ≤ 7 ^ q := pow_le_pow_left' (by omega) q
    _ ≤ 7 ^ (q + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ q)

/-- The normalized rational coordinate attached to a weak composition.-/
def gamma {q : ℕ} (k : EvertseGammaIndex q) (i : Fin q) : ℝ :=
  (k.1 i : ℕ) / (2 * q : ℝ)

/-- Every normalized exponent coordinate is nonnegative.-/
theorem gamma_nonneg {q : ℕ} (k : EvertseGammaIndex q) (i : Fin q) :
    0 ≤ k.gamma i := by
  unfold gamma
  positivity

/-- The normalized coordinates of a weak composition sum to `1/2`.-/
theorem sum_gamma {q : ℕ} (hq : 0 < q) (k : EvertseGammaIndex q) :
    ∑ i, k.gamma i = (1 / 2 : ℝ) := by
  unfold gamma
  rw [← Finset.sum_div]
  have hsum : ∑ i, ((k.1 i : ℕ) : ℝ) = q := by
    exact_mod_cast k.2
  rw [hsum]
  field_simp

end EvertseGammaIndex

private theorem exists_bounded_allocation {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ) (n : ℕ)
    (h : n ≤ ∑ i ∈ s, a i) :
    ∃ k : ι → ℕ, (∀ i ∈ s, k i ≤ a i) ∧ ∑ i ∈ s, k i = n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
      simp only [Finset.sum_empty, nonpos_iff_eq_zero] at h
      subst n
      exact ⟨fun _ => 0, by simp⟩
  | @insert i s hi ih =>
      let ki := min n (a i)
      have hrem : n - ki ≤ ∑ j ∈ s, a j := by
        by_cases hn : n ≤ a i
        · simp [ki, min_eq_left hn]
        · simp only [ki, min_eq_right (Nat.le_of_not_ge hn)]
          rw [Finset.sum_insert hi] at h
          omega
      obtain ⟨k, hk, hksum⟩ := ih (n - ki) hrem
      refine ⟨Function.update k i ki, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [ki]
        · have hji : j ≠ i := by
            intro hji
            subst j
            exact hi hj
          simpa [Function.update, hji] using hk j hj
      · rw [Finset.sum_insert hi]
        simp only [Function.update_self]
        have hup : ∑ j ∈ s, Function.update k i ki j = ∑ j ∈ s, k j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hi hj
          simp [Function.update, hji]
        rw [hup, hksum]
        exact Nat.add_sub_of_le (Nat.min_le_left _ _)

private theorem floor_allocation_sum_ge {q : ℕ} (alpha : Fin q → ℝ)
    (hsum : 1 ≤ ∑ i, alpha i) :
    q ≤ ∑ i, ⌊(2 * q : ℝ) * alpha i⌋₊ := by
  have hterm (i : Fin q) :
      (2 * q : ℝ) * alpha i ≤
        (⌊(2 * q : ℝ) * alpha i⌋₊ : ℝ) + 1 := by
    exact (Nat.lt_floor_add_one _).le
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hleft : (2 * q : ℝ) ≤ ∑ i, (⌊(2 * q : ℝ) * alpha i⌋₊ : ℝ) + q := by
    calc
      (2 * q : ℝ) = (2 * q : ℝ) * 1 := by ring
      _ ≤ (2 * q : ℝ) * ∑ i, alpha i :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ∑ i, (2 * q : ℝ) * alpha i := by
        rw [Finset.mul_sum]
      _ ≤ _ := hs
  have hcast : (q : ℝ) ≤ ∑ i, (⌊(2 * q : ℝ) * alpha i⌋₊ : ℝ) := by
    linarith
  exact_mod_cast hcast

/-- Every nonnegative vector of total mass at least one dominates one of the normalized weak composition vectors.-/
theorem EvertseGammaIndex.exists_gamma_le {q : ℕ} (hq : 0 < q)
    (alpha : Fin q → ℝ) (halpha : ∀ i, 0 ≤ alpha i)
    (hsum : 1 ≤ ∑ i, alpha i) :
    ∃ k : EvertseGammaIndex q, ∀ i, k.gamma i ≤ alpha i := by
  let a : Fin q → ℕ := fun i => ⌊(2 * q : ℝ) * alpha i⌋₊
  have hqa : q ≤ ∑ i ∈ Finset.univ, a i := by
    simpa [a] using floor_allocation_sum_ge alpha hsum
  obtain ⟨k, hk, hksum⟩ :=
    exists_bounded_allocation Finset.univ a q hqa
  have hkle (i : Fin q) : k i ≤ q := by
    calc
      k i ≤ ∑ j ∈ Finset.univ, k j := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = q := hksum
  let kfin : Fin q → Fin (q + 1) := fun i => ⟨k i, Nat.lt_succ_of_le (hkle i)⟩
  have hkfin_sum : ∑ i, (kfin i : ℕ) = q := by
    simpa [kfin] using hksum
  let K : EvertseGammaIndex q := ⟨kfin, hkfin_sum⟩
  refine ⟨K, fun i => ?_⟩
  have hkfloor : (k i : ℝ) ≤ (a i : ℝ) := by
    exact_mod_cast hk i (Finset.mem_univ i)
  have hfloor : (a i : ℝ) ≤ (2 * q : ℝ) * alpha i := by
    apply Nat.floor_le
    exact mul_nonneg (by positivity) (halpha i)
  have hden : (0 : ℝ) < 2 * q := by positivity
  change (k i : ℝ) / (2 * q : ℝ) ≤ alpha i
  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using hkfloor.trans hfloor

/-- A normalized simplex coordinate indexed by an arbitrary finite type.-/
def evertseLocalGamma {ι : Type*} [Fintype ι]
    (k : EvertseGammaIndex (Fintype.card ι)) (i : ι) : ℝ :=
  k.gamma (Fintype.equivFin ι i)

/-- Local simplex coordinates are nonnegative.-/
theorem evertseLocalGamma_nonneg {ι : Type*} [Fintype ι]
    (k : EvertseGammaIndex (Fintype.card ι)) (i : ι) :
    0 ≤ evertseLocalGamma k i :=
  EvertseGammaIndex.gamma_nonneg _ _

/-- The local simplex coordinates sum to `1/2`.-/
theorem sum_evertseLocalGamma_eq_half {ι : Type*} [Fintype ι] [Nonempty ι]
    (k : EvertseGammaIndex (Fintype.card ι)) :
    ∑ i, evertseLocalGamma k i = (1 / 2 : ℝ) := by
  rw [show ∑ i, evertseLocalGamma k i = ∑ j, k.gamma j by
    exact (Fintype.equivFin ι).sum_comp k.gamma]
  exact EvertseGammaIndex.sum_gamma (Fintype.card_pos_iff.mpr inferInstance) k

/-- The finite simplex cover, stated invariantly over an arbitrary nonempty finite type.-/
theorem exists_evertseLocalGamma_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (alpha : ι → ℝ) (halpha : ∀ i, 0 ≤ alpha i)
    (hsum : 1 ≤ ∑ i, alpha i) :
    ∃ k : EvertseGammaIndex (Fintype.card ι),
      ∀ i, evertseLocalGamma k i ≤ alpha i := by
  let e := Fintype.equivFin ι
  let alphaFin : Fin (Fintype.card ι) → ℝ := fun j => alpha (e.symm j)
  have hsumFin : 1 ≤ ∑ j, alphaFin j := by
    rw [show ∑ j, alphaFin j = ∑ i, alpha i by
      exact e.symm.sum_comp alpha]
    exact hsum
  obtain ⟨k, hk⟩ := EvertseGammaIndex.exists_gamma_le
    (Fintype.card_pos_iff.mpr inferInstance) alphaFin
    (fun j => halpha (e.symm j)) hsumFin
  refine ⟨k, fun i => ?_⟩
  simpa [evertseLocalGamma, alphaFin, e] using hk (e i)

/-- The invariant simplex carrier has at most `7^(q+1)` elements.-/
theorem evertseGammaIndex_card_le {ι : Type*} [Fintype ι] :
    Fintype.card (EvertseGammaIndex (Fintype.card ι)) ≤
      7 ^ (Fintype.card ι + 1) :=
  EvertseGammaIndex.card_le_seven_pow _

/-! ## Exact base-field height normalization -/

/-! ## Logarithmic local losses and the high-height simplex cover -/

/-- The local logarithmic loss of a positive factor `f i ≤ 1`, normalized by `log H`.-/
def evertseLogarithmicLoss {ι : Type*} [Fintype ι]
    (H : ℝ) (f : ι → ℝ) (i : ι) : ℝ :=
  -Real.log (f i) / Real.log H

/-- Normalized logarithmic losses are nonnegative.-/
theorem evertseLogarithmicLoss_nonneg {ι : Type*} [Fintype ι]
    {H : ℝ} (hH : 1 < H) {f : ι → ℝ}
    (hfpos : ∀ i, 0 < f i) (hfle : ∀ i, f i ≤ 1) (i : ι) :
    0 ≤ evertseLogarithmicLoss H f i := by
  unfold evertseLogarithmicLoss
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (hfpos i).le (hfle i)))
    (Real.log_nonneg (le_of_lt hH))

/-- A product saving of `H⁻¹` supplies total normalized logarithmic loss at least one.-/
theorem one_le_sum_evertseLogarithmicLoss
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {H : ℝ} (hH : 1 < H) {f : ι → ℝ}
    (hfpos : ∀ i, 0 < f i) (hprod : ∏ i, f i ≤ H⁻¹) :
    1 ≤ ∑ i, evertseLogarithmicLoss H f i := by
  have hprodpos : 0 < ∏ i, f i := Finset.prod_pos fun i _hi => hfpos i
  have hlog := Real.log_le_log hprodpos hprod
  rw [Real.log_inv] at hlog
  have hlogH : 0 < Real.log H := Real.log_pos hH
  unfold evertseLogarithmicLoss
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Real.log_prod]
  · apply (le_div_iff₀ hlogH).2
    linarith
  · exact fun i _hi => (hfpos i).ne'

/-- Comparing a normalized logarithmic loss with `g` is equivalent to the multiplicative estimate `f ≤ H⁻ᵍ`.-/
theorem evertseLogarithmicLoss_bound_iff
    {H f : ℝ} (hH : 1 < H) (hf : 0 < f) {g : ℝ} :
    g ≤ -Real.log f / Real.log H ↔ f ≤ H ^ (-g : ℝ) := by
  have hlogH : 0 < Real.log H := Real.log_pos hH
  rw [le_div_iff₀ hlogH]
  constructor
  · intro h
    apply (Real.log_le_log_iff hf (Real.rpow_pos_of_pos (by positivity) _)).mp
    rw [Real.log_rpow (by positivity)]
    linarith
  · intro h
    have hlog := Real.log_le_log hf h
    rw [Real.log_rpow (by positivity)] at hlog
    linarith

/-- Multiplicative product savings are covered by one of the finitely many simplex systems.-/
theorem exists_evertseGamma_rpow_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {H : ℝ} (hH : 1 < H) {f : ι → ℝ}
    (hfpos : ∀ i, 0 < f i) (hfle : ∀ i, f i ≤ 1)
    (hprod : ∏ i, f i ≤ H⁻¹) :
    ∃ k : EvertseGammaIndex (Fintype.card ι),
      ∀ i, f i ≤ H ^ (-evertseLocalGamma k i : ℝ) := by
  obtain ⟨k, hk⟩ := exists_evertseLocalGamma_le
    (evertseLogarithmicLoss H f)
    (evertseLogarithmicLoss_nonneg hH hfpos hfle)
    (one_le_sum_evertseLogarithmicLoss hH hfpos hprod)
  exact ⟨k, fun i =>
    (evertseLogarithmicLoss_bound_iff hH (hfpos i)).mp (hk i)⟩

/-- The normalized small-part factor at one retained place and one target root.-/
def evertsePlaceNormalizedCloseness
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z root : EvertseCubicField) : ℝ :=
  match v with
  | Sum.inl w => min 1 (w (z - root))
  | Sum.inr w => Real.sqrt (min 1 (w.1 (z - root)))

/-- The product of the three root-closeness factors at a retained local place.-/
def evertseTriplePlaceCloseness
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z : EvertseCubicField) : ℝ :=
  evertsePlaceNormalizedCloseness v z 1 *
    evertsePlaceNormalizedCloseness v z evertseRho *
    evertsePlaceNormalizedCloseness v z (evertseRho ^ 2)

/-! ## Pair determinants and the four-point Vandermonde kernel -/

/-- On the affine line `x+y=1`, the projective determinant is simply `x₁-x₂`.-/
theorem evertseSolution_determinant_eq_sub
    {S : Finset ℕ} {x₁ y₁ x₂ y₂ : ℚ}
    (hsol₁ : IsRationalSUnitEquationSolution S x₁ y₁)
    (hsol₂ : IsRationalSUnitEquationSolution S x₂ y₂) :
    x₁ * y₂ - x₂ * y₁ = x₁ - x₂ := by
  have hy₁ : y₁ = 1 - x₁ := by linarith [hsol₁.2.2]
  have hy₂ : y₂ = 1 - x₂ := by linarith [hsol₂.2.2]
  rw [hy₁, hy₂]
  ring

/-- The four-point Vandermonde matrix in Evertse's quadratic field.-/
def evertseFourPointVandermonde (z : Fin 4 → EvertseCubicField) :
    Matrix (Fin 4) (Fin 4) EvertseCubicField :=
  Matrix.vandermonde z

/-! ## A local four-point pigeonhole estimate -/

/-- The three roots targeted by Evertse's cubic transformation.-/
def evertseThreeRoots : Fin 3 → EvertseCubicField :=
  ![1, evertseRho, evertseRho ^ 2]

/-- The raw, unnormalized closeness of a point to one target root at an absolute value.-/
def evertseRawCloseness (v : AbsoluteValue EvertseCubicField ℝ)
    (z root : EvertseCubicField) : ℝ :=
  min 1 (v (z - root))

/-- The product of the three raw root-closeness factors at one absolute value.-/
def evertseRawTripleCloseness (v : AbsoluteValue EvertseCubicField ℝ)
    (z : EvertseCubicField) : ℝ :=
  evertseRawCloseness v z (evertseThreeRoots 0) *
    evertseRawCloseness v z (evertseThreeRoots 1) *
    evertseRawCloseness v z (evertseThreeRoots 2)

/-- A root at which the raw local closeness of `z` is minimal.-/
def evertseClosestRoot (v : AbsoluteValue EvertseCubicField ℝ)
    (z : EvertseCubicField) : Fin 3 :=
  Classical.choose (Finset.exists_min_image Finset.univ
    (fun r : Fin 3 => evertseRawCloseness v z (evertseThreeRoots r))
    Finset.univ_nonempty)

/-- The selected root minimizes raw local closeness among the three target roots.-/
theorem evertseClosestRoot_le (v : AbsoluteValue EvertseCubicField ℝ)
    (z : EvertseCubicField) (r : Fin 3) :
    evertseRawCloseness v z (evertseThreeRoots (evertseClosestRoot v z)) ≤
      evertseRawCloseness v z (evertseThreeRoots r) := by
  exact (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun r : Fin 3 => evertseRawCloseness v z (evertseThreeRoots r))
    Finset.univ_nonempty)).2 r (Finset.mem_univ r)

/-- Raw local closeness is nonnegative.-/
theorem evertseRawCloseness_nonneg (v : AbsoluteValue EvertseCubicField ℝ)
    (z root : EvertseCubicField) :
    0 ≤ evertseRawCloseness v z root :=
  le_min (by norm_num) (v.nonneg _)

/-- The cube of the least root-closeness is at most the product of all three.-/
theorem evertseClosestRoot_cube_le_triple
    (v : AbsoluteValue EvertseCubicField ℝ) (z : EvertseCubicField) :
    evertseRawCloseness v z (evertseThreeRoots (evertseClosestRoot v z)) ^ 3 ≤
      evertseRawTripleCloseness v z := by
  let c := evertseRawCloseness v z
    (evertseThreeRoots (evertseClosestRoot v z))
  have hc0 : 0 ≤ c := evertseRawCloseness_nonneg _ _ _
  have h0 : c ≤ evertseRawCloseness v z (evertseThreeRoots 0) :=
    evertseClosestRoot_le _ _ _
  have h1 : c ≤ evertseRawCloseness v z (evertseThreeRoots 1) :=
    evertseClosestRoot_le _ _ _
  have h2 : c ≤ evertseRawCloseness v z (evertseThreeRoots 2) :=
    evertseClosestRoot_le _ _ _
  unfold evertseRawTripleCloseness
  change c ^ 3 ≤ _
  rw [pow_succ, pow_two]
  have hp : c * c ≤
      evertseRawCloseness v z (evertseThreeRoots 0) *
        evertseRawCloseness v z (evertseThreeRoots 1) :=
    mul_le_mul h0 h1 hc0 (evertseRawCloseness_nonneg _ _ _)
  exact mul_le_mul hp h2 hc0
    (mul_nonneg (evertseRawCloseness_nonneg _ _ _)
      (evertseRawCloseness_nonneg _ _ _))

/-- Closeness of two points is bounded by their closeness to a common root.-/
theorem evertseRawCloseness_sub_le_add
    (v : AbsoluteValue EvertseCubicField ℝ)
    (z w root : EvertseCubicField) :
    min 1 (v (z - w)) ≤
      evertseRawCloseness v z root + evertseRawCloseness v w root := by
  have htri : v (z - w) ≤ v (z - root) + v (w - root) := by
    calc
      v (z - w) = v ((z - root) + (root - w)) := by congr 1; ring
      _ ≤ v (z - root) + v (root - w) := v.add_le _ _
      _ = v (z - root) + v (w - root) := by
        congr 1
        rw [show root - w = -(w - root) by ring, map_neg_eq_map]
  by_cases hz : 1 ≤ v (z - root)
  · have hone : 1 ≤
        evertseRawCloseness v z root + evertseRawCloseness v w root := by
      rw [evertseRawCloseness, min_eq_left hz]
      exact le_add_of_nonneg_right (evertseRawCloseness_nonneg _ _ _)
    exact (min_le_left _ _).trans hone
  · have hz' : v (z - root) ≤ 1 := le_of_not_ge hz
    by_cases hw : 1 ≤ v (w - root)
    · have hone : 1 ≤
          evertseRawCloseness v z root + evertseRawCloseness v w root := by
        change 1 ≤ min 1 (v (z - root)) + min 1 (v (w - root))
        rw [min_eq_left hw]
        exact le_add_of_nonneg_left (evertseRawCloseness_nonneg _ _ _)
      exact (min_le_left _ _).trans hone
    · have hw' : v (w - root) ≤ 1 := le_of_not_ge hw
      rw [evertseRawCloseness, min_eq_right hz',
        evertseRawCloseness, min_eq_right hw']
      exact (min_le_right _ _).trans htri

/-- Among four points, two are closest to the same one of the three roots.-/
theorem exists_pair_evertseRawVandermonde_local
    (v : AbsoluteValue EvertseCubicField ℝ)
    (z : Fin 4 → EvertseCubicField) :
    ∃ i j : Fin 4, i ≠ j ∧
      min 1 (v (z i - z j)) ^ 3 ≤
        8 * max (evertseRawTripleCloseness v (z i))
          (evertseRawTripleCloseness v (z j)) := by
  obtain ⟨i, j, hij, hroot⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin 4 => evertseClosestRoot v (z i)) (by norm_num)
  refine ⟨i, j, hij, ?_⟩
  let ci := evertseRawCloseness v (z i)
    (evertseThreeRoots (evertseClosestRoot v (z i)))
  let cj := evertseRawCloseness v (z j)
    (evertseThreeRoots (evertseClosestRoot v (z j)))
  have hdiff : min 1 (v (z i - z j)) ≤ ci + cj := by
    simpa [ci, cj, hroot] using evertseRawCloseness_sub_le_add
      v (z i) (z j) (evertseThreeRoots (evertseClosestRoot v (z i)))
  have hci0 : 0 ≤ ci := evertseRawCloseness_nonneg _ _ _
  have hcj0 : 0 ≤ cj := evertseRawCloseness_nonneg _ _ _
  have hdiff0 : 0 ≤ min 1 (v (z i - z j)) :=
    le_min (by norm_num) (v.nonneg _)
  have hsum : ci + cj ≤ 2 * max ci cj := by
    calc
      ci + cj ≤ max ci cj + max ci cj :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max ci cj := by ring
  have hcub : min 1 (v (z i - z j)) ^ 3 ≤ 8 * (max ci cj) ^ 3 := by
    have hh := pow_le_pow_left₀ hdiff0 (hdiff.trans hsum) 3
    calc
      min 1 (v (z i - z j)) ^ 3 ≤ (2 * max ci cj) ^ 3 := hh
      _ = 8 * (max ci cj) ^ 3 := by ring
  have hmaxcube : (max ci cj) ^ 3 ≤
      max (evertseRawTripleCloseness v (z i))
        (evertseRawTripleCloseness v (z j)) := by
    by_cases h : ci ≤ cj
    · rw [max_eq_right h]
      exact (evertseClosestRoot_cube_le_triple v (z j)).trans
        (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge h)]
      exact (evertseClosestRoot_cube_le_triple v (z i)).trans
        (le_max_left _ _)
  exact hcub.trans (mul_le_mul_of_nonneg_left hmaxcube (by norm_num))

/-- At an infinite place, normalized closeness is raw closeness.-/
theorem evertsePlaceNormalizedCloseness_infinite_eq_raw
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (w : NumberField.InfinitePlace EvertseCubicField)
    (z root : EvertseCubicField) :
    evertsePlaceNormalizedCloseness (S := S) (hS := hS) (Sum.inl w) z root =
      evertseRawCloseness w.1 z root :=
  rfl

/-- At a finite place, the square of normalized closeness is raw closeness.-/
theorem evertsePlaceNormalizedCloseness_finite_sq_eq_raw
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (w : {w : NumberField.FinitePlace EvertseCubicField //
      w ∈ evertseExceptionalFinitePlaces S hS})
    (z root : EvertseCubicField) :
    evertsePlaceNormalizedCloseness (S := S) (hS := hS)
        (Sum.inr w) z root ^ 2 = evertseRawCloseness w.1.1 z root := by
  unfold evertsePlaceNormalizedCloseness evertseRawCloseness
  exact Real.sq_sqrt (le_min (by norm_num) (w.1.1.nonneg _))

/-- At an infinite place, normalized and raw triple closeness agree.-/
theorem evertseTriplePlaceCloseness_infinite_eq_raw
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (w : NumberField.InfinitePlace EvertseCubicField)
    (z : EvertseCubicField) :
    evertseTriplePlaceCloseness (S := S) (hS := hS) (Sum.inl w) z =
      evertseRawTripleCloseness w.1 z :=
  rfl

/-- At a finite place, the square of normalized triple closeness is the raw product.-/
theorem evertseTriplePlaceCloseness_finite_sq_eq_raw
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (w : {w : NumberField.FinitePlace EvertseCubicField //
      w ∈ evertseExceptionalFinitePlaces S hS})
    (z : EvertseCubicField) :
    evertseTriplePlaceCloseness (S := S) (hS := hS) (Sum.inr w) z ^ 2 =
      evertseRawTripleCloseness w.1.1 z := by
  unfold evertseTriplePlaceCloseness evertseRawTripleCloseness
  rw [show evertseThreeRoots 0 = 1 by simp [evertseThreeRoots],
    show evertseThreeRoots 1 = evertseRho by simp [evertseThreeRoots],
    show evertseThreeRoots 2 = evertseRho ^ 2 by simp [evertseThreeRoots]]
  rw [mul_pow, mul_pow, evertsePlaceNormalizedCloseness_finite_sq_eq_raw,
    evertsePlaceNormalizedCloseness_finite_sq_eq_raw,
    evertsePlaceNormalizedCloseness_finite_sq_eq_raw]

/-- Normalized placewise closeness is nonnegative.-/
theorem evertsePlaceNormalizedCloseness_nonneg
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z root : EvertseCubicField) :
    0 ≤ evertsePlaceNormalizedCloseness v z root := by
  rcases v with w | w
  · exact le_min (by norm_num) (w.1.nonneg _)
  · exact Real.sqrt_nonneg _

/-- Normalized triple closeness is nonnegative.-/
theorem evertseTriplePlaceCloseness_nonneg
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z : EvertseCubicField) :
    0 ≤ evertseTriplePlaceCloseness v z := by
  unfold evertseTriplePlaceCloseness
  exact mul_nonneg
    (mul_nonneg (evertsePlaceNormalizedCloseness_nonneg _ _ _)
      (evertsePlaceNormalizedCloseness_nonneg _ _ _))
    (evertsePlaceNormalizedCloseness_nonneg _ _ _)

private theorem max_sq_eq_max_sq_of_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ^ 2 = max (a ^ 2) (b ^ 2) := by
  by_cases h : a ≤ b
  · have hs : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha h 2
    rw [max_eq_right h, max_eq_right hs]
  · have h' : b ≤ a := le_of_not_ge h
    have hs : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb h' 2
    rw [max_eq_left h', max_eq_left hs]

/-- The four-point local pigeonhole estimate in the normalized place convention.-/
theorem exists_pair_evertsePlaceVandermonde_local
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z : Fin 4 → EvertseCubicField) :
    ∃ i j : Fin 4, i ≠ j ∧
      evertsePlaceNormalizedCloseness v (z i) (z j) ^ 3 ≤
        8 * max (evertseTriplePlaceCloseness v (z i))
          (evertseTriplePlaceCloseness v (z j)) := by
  rcases v with w | w
  · simpa [evertseRawCloseness,
      evertsePlaceNormalizedCloseness_infinite_eq_raw,
      evertseTriplePlaceCloseness_infinite_eq_raw] using
      exists_pair_evertseRawVandermonde_local w.1 z
  · obtain ⟨i, j, hij, hraw⟩ :=
      exists_pair_evertseRawVandermonde_local w.1.1 z
    refine ⟨i, j, hij, ?_⟩
    let d := evertsePlaceNormalizedCloseness (Sum.inr w) (z i) (z j)
    let ti := evertseTriplePlaceCloseness (Sum.inr w) (z i)
    let tj := evertseTriplePlaceCloseness (Sum.inr w) (z j)
    have hd0 : 0 ≤ d := evertsePlaceNormalizedCloseness_nonneg _ _ _
    have hti0 : 0 ≤ ti := evertseTriplePlaceCloseness_nonneg _ _
    have htj0 : 0 ≤ tj := evertseTriplePlaceCloseness_nonneg _ _
    have hd2 : d ^ 2 = evertseRawCloseness w.1.1 (z i) (z j) :=
      evertsePlaceNormalizedCloseness_finite_sq_eq_raw w _ _
    have hti2 : ti ^ 2 = evertseRawTripleCloseness w.1.1 (z i) :=
      evertseTriplePlaceCloseness_finite_sq_eq_raw w _
    have htj2 : tj ^ 2 = evertseRawTripleCloseness w.1.1 (z j) :=
      evertseTriplePlaceCloseness_finite_sq_eq_raw w _
    have hmax2 : max ti tj ^ 2 =
        max (evertseRawTripleCloseness w.1.1 (z i))
          (evertseRawTripleCloseness w.1.1 (z j)) := by
      rw [max_sq_eq_max_sq_of_nonneg hti0 htj0, hti2, htj2]
    change d ^ 3 ≤ 8 * max ti tj
    have hsquare : (d ^ 3) ^ 2 ≤ (8 * max ti tj) ^ 2 := by
      rw [← pow_mul, show 3 * 2 = 6 by norm_num,
        show d ^ 6 = (d ^ 2) ^ 3 by ring, hd2]
      rw [mul_pow, hmax2]
      exact hraw.trans (by
        apply mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 8 ^ 2)
        have hrawi : 0 ≤ evertseRawTripleCloseness w.1.1 (z i) := by
          unfold evertseRawTripleCloseness
          exact mul_nonneg
            (mul_nonneg (evertseRawCloseness_nonneg _ _ _)
              (evertseRawCloseness_nonneg _ _ _))
            (evertseRawCloseness_nonneg _ _ _)
        exact hrawi.trans (le_max_left _ _))
    exact (sq_le_sq₀ (by positivity : 0 ≤ d ^ 3)
      (by positivity : 0 ≤ 8 * max ti tj)).mp hsquare

/-! ## Selecting and averaging the local exceptional pair -/

/-- One of the six unordered pairs of four indices, represented in increasing order.-/
abbrev EvertseFourPair := {p : Fin 4 × Fin 4 // p.1 < p.2}

/-- There are exactly six unordered pairs of four indices.-/
theorem card_evertseFourPair : Fintype.card EvertseFourPair = 6 := by
  decide

/-- Normalized local closeness is symmetric in its two field arguments.-/
theorem evertsePlaceNormalizedCloseness_symm
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z w : EvertseCubicField) :
    evertsePlaceNormalizedCloseness v z w =
      evertsePlaceNormalizedCloseness v w z := by
  rcases v with v | v
  · change min 1 (v.1 (z - w)) = min 1 (v.1 (w - z))
    have habv : v.1 (z - w) = v.1 (w - z) := by
      rw [show z - w = -(w - z) by ring, map_neg_eq_map]
    rw [habv]
  · change Real.sqrt (min 1 (v.1.1 (z - w))) =
      Real.sqrt (min 1 (v.1.1 (w - z)))
    have habv : v.1.1 (z - w) = v.1.1 (w - z) := by
      rw [show z - w = -(w - z) by ring, map_neg_eq_map]
    rw [habv]

/-- Canonical unordered-pair form of the normalized local four-point estimate.-/
theorem exists_evertseFourPair_local
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z : Fin 4 → EvertseCubicField) :
    ∃ p : EvertseFourPair,
      evertsePlaceNormalizedCloseness v (z p.1.1) (z p.1.2) ^ 3 ≤
        8 * max (evertseTriplePlaceCloseness v (z p.1.1))
          (evertseTriplePlaceCloseness v (z p.1.2)) := by
  obtain ⟨i, j, hij, hbound⟩ :=
    exists_pair_evertsePlaceVandermonde_local v z
  by_cases hlt : i < j
  · exact ⟨⟨(i, j), hlt⟩, hbound⟩
  · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    refine ⟨⟨(j, i), hjlt⟩, ?_⟩
    simpa [evertsePlaceNormalizedCloseness_symm, max_comm] using hbound

/-- The canonical exceptional pair selected at one retained place.-/
def evertseLocalFourPair
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (z : Fin 4 → EvertseCubicField) :
    EvertseFourPair :=
  Classical.choose (exists_evertseFourPair_local v z)

/-- Retained places whose locally selected exceptional pair is `p`.-/
def evertseFourPairPlaceSet
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (z : Fin 4 → EvertseCubicField) (p : EvertseFourPair) :
    Finset (EvertsePlace S hS) :=
  Finset.univ.filter fun v => evertseLocalFourPair v z = p

/-! ## The fixed-simplex selected-pair product bound -/

/-! ## Product-formula lower bounds for selected retained places -/

/-! ## The global fixed-simplex gap kernel -/

/-! ## Clearing the cubic-transform denominators -/

/-- The homogeneous cubic Veronese matrix of the four transformed solution pairs.-/
def evertseFourPointProjectiveVandermonde
    (x y : Fin 4 → ℚ) : Matrix (Fin 4) (Fin 4) EvertseCubicField :=
  Matrix.projVandermonde (fun i => evertseXi (x i) (y i))
    (fun i => evertseEta (x i) (y i))

/-! ## Finite bounded-height fibers of the high branch -/

/-- The finite rational height ball with an arbitrary real cutoff.-/
def evertseRationalHeightBall (B : ℝ) : Finset ℚ :=
  (finite_rationalHeight_le B).toFinset

@[simp]
theorem mem_evertseRationalHeightBall {B : ℝ} {q : ℚ} :
    q ∈ evertseRationalHeightBall B ↔ rationalHeight q ≤ B := by
  simp [evertseRationalHeightBall]

/-- Ratios of rational unit-equation solutions with height at most `B`.-/
def boundedRationalSUnitEquationRatioSet
    (S : Finset ℕ) (B : ℝ) : Finset ℚ := by
  classical
  exact (evertseRationalHeightBall B).filter fun q =>
    IsRationalSUnitEquationSolution S
      (rationalEquationPairOfRatio q).1 (rationalEquationPairOfRatio q).2

/-- Exact finite carrier for rational unit-equation solutions whose ratio height is at most `B`.-/
def boundedRationalSUnitEquationCarrier
    (S : Finset ℕ) (B : ℝ) : Finset (ℚ × ℚ) :=
  (boundedRationalSUnitEquationRatioSet S B).image rationalEquationPairOfRatio

/-- Predicate for a rational unit-equation solution with bounded ratio height.-/
def IsBoundedRationalSUnitEquationSolution
    (S : Finset ℕ) (B : ℝ) (x y : ℚ) : Prop :=
  IsRationalSUnitEquationSolution S x y ∧ rationalHeight (x / y) ≤ B

/-- Membership in the bounded carrier is exactly the bounded solution predicate.-/
@[simp]
theorem mem_boundedRationalSUnitEquationCarrier
    {S : Finset ℕ} {B : ℝ} {x y : ℚ} :
    (x, y) ∈ boundedRationalSUnitEquationCarrier S B ↔
      IsBoundedRationalSUnitEquationSolution S B x y := by
  classical
  constructor
  · intro hxy
    obtain ⟨q, hq, hpair⟩ := Finset.mem_image.mp hxy
    change q ∈ (evertseRationalHeightBall B).filter (fun q =>
      IsRationalSUnitEquationSolution S
        (rationalEquationPairOfRatio q).1
        (rationalEquationPairOfRatio q).2) at hq
    obtain ⟨hqB, hsol⟩ := Finset.mem_filter.mp hq
    have hqAdd : q + 1 ≠ 0 := by
      intro hz
      exact hsol.2.1.ne_zero (by simp [rationalEquationPairOfRatio, hz])
    have hratio := rationalEquationPairOfRatio_ratio_of_ne hqAdd
    have hbounded : IsBoundedRationalSUnitEquationSolution S B
        (rationalEquationPairOfRatio q).1
        (rationalEquationPairOfRatio q).2 :=
      ⟨hsol, by
        rw [hratio]
        exact mem_evertseRationalHeightBall.mp hqB⟩
    simpa only [hpair] using hbounded
  · rintro ⟨hsol, hB⟩
    let q := x / y
    have hpair : rationalEquationPairOfRatio q = (x, y) :=
      rationalEquationPairOfRatio_eq_of_solution hsol
    apply Finset.mem_image.mpr
    refine ⟨q, show q ∈ boundedRationalSUnitEquationRatioSet S B from
      Finset.mem_filter.mpr
        ⟨mem_evertseRationalHeightBall.mpr hB, ?_⟩, hpair⟩
    simpa only [hpair] using hsol

/-- Predicate for the high-height branch of the rational unit equation.-/
def IsHighRationalSUnitEquationSolution
    (S : Finset ℕ) (x y : ℚ) : Prop :=
  IsRationalSUnitEquationSolution S x y ∧
    lowHeightCutoff49 < rationalHeight (x / y)

/-- Bounded-height carrier for the high branch.-/
def boundedHighRationalSUnitEquationCarrier
    (S : Finset ℕ) (B : ℝ) : Finset (ℚ × ℚ) :=
  (boundedRationalSUnitEquationCarrier S B).filter fun z =>
    lowHeightCutoff49 < rationalHeight (z.1 / z.2)

/-- Exact membership theorem for the bounded high branch.-/
@[simp]
theorem mem_boundedHighRationalSUnitEquationCarrier
    {S : Finset ℕ} {B : ℝ} {x y : ℚ} :
    (x, y) ∈ boundedHighRationalSUnitEquationCarrier S B ↔
      IsHighRationalSUnitEquationSolution S x y ∧
        rationalHeight (x / y) ≤ B := by
  rw [boundedHighRationalSUnitEquationCarrier, Finset.mem_filter,
    mem_boundedRationalSUnitEquationCarrier]
  constructor
  · rintro ⟨⟨hsol, hB⟩, hhigh⟩
    exact ⟨⟨hsol, hhigh⟩, hB⟩
  · rintro ⟨⟨hsol, hhigh⟩, hB⟩
    exact ⟨⟨hsol, hB⟩, hhigh⟩

/-- A high solution belongs to the fixed local simplex system `k`.-/
def IsInEvertseGamma
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (k : EvertseGammaIndex (Fintype.card (EvertsePlace S hS)))
    (x y : ℚ) : Prop :=
  IsHighRationalSUnitEquationSolution S x y ∧ ∀ v,
    evertseTriplePlaceCloseness v (evertseZeta x y) ≤
      evertseNormalizedHeight (evertseZeta x y) ^
        (-evertseLocalGamma k v : ℝ)

/-- Finite bounded-height fiber of one local simplex system.-/
def boundedEvertseGammaCarrier
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (B : ℝ)
    (k : EvertseGammaIndex (Fintype.card (EvertsePlace S hS))) :
    Finset (ℚ × ℚ) := by
  classical
  exact (boundedHighRationalSUnitEquationCarrier S B).filter fun z =>
    IsInEvertseGamma hS k z.1 z.2

/-- Exact membership theorem for a bounded fixed-simplex fiber.-/
@[simp]
theorem mem_boundedEvertseGammaCarrier
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime} {B : ℝ}
    {k : EvertseGammaIndex (Fintype.card (EvertsePlace S hS))}
    {x y : ℚ} :
    (x, y) ∈ boundedEvertseGammaCarrier hS B k ↔
      IsInEvertseGamma hS k x y ∧ rationalHeight (x / y) ≤ B := by
  classical
  rw [boundedEvertseGammaCarrier, Finset.mem_filter,
    mem_boundedHighRationalSUnitEquationCarrier]
  constructor
  · rintro ⟨⟨_hhigh, hB⟩, hgamma⟩
    exact ⟨hgamma, hB⟩
  · rintro ⟨hgamma, hB⟩
    exact ⟨⟨hgamma.1, hB⟩, hgamma⟩

/-! ## Four points in one local simplex system -/

/-- An index where the four transformed points have minimum normalized height.-/
def evertseFourPointMinHeightIndex
    (z : Fin 4 → EvertseCubicField) : Fin 4 :=
  Classical.choose (Finset.exists_min_image Finset.univ
    (fun i => evertseNormalizedHeight (z i)) Finset.univ_nonempty)

/-- The minimum normalized height among four transformed points.-/
def evertseFourPointMinHeight
    (z : Fin 4 → EvertseCubicField) : ℝ :=
  evertseNormalizedHeight (z (evertseFourPointMinHeightIndex z))

/-- On the affine line `x+y=1`, injectivity of solution pairs implies injectivity of their first coordinates.-/
theorem evertseFirstCoordinate_injective_of_pair_injective
    {S : Finset ℕ} (u : Fin 4 → ℚ × ℚ)
    (hu : ∀ i, IsRationalSUnitEquationSolution S (u i).1 (u i).2)
    (hinj : Function.Injective u) :
    Function.Injective (fun i => (u i).1) := by
  intro i j hx
  apply hinj
  apply Prod.ext hx
  linarith [(hu i).2.2, (hu j).2.2]

/-- The complete degree-three Veronese row in two homogeneous variables.-/
def evertseCubicVeronese
    (X E : EvertseCubicField) : Fin 4 → EvertseCubicField :=
  fun j ↦ X ^ j.1 * E ^ j.rev.1

/-! ## Normalized projective products over all places -/

/-- The projective sup norm at an infinite place of the quadratic field.-/
def evertseInfiniteProjectiveNorm
    (w : NumberField.InfinitePlace EvertseCubicField)
    (X E : EvertseCubicField) : ℝ :=
  max (w X) (w E)

/-- The square-root-normalized projective sup norm at a finite place.-/
def evertseFiniteProjectiveNorm
    (w : NumberField.FinitePlace EvertseCubicField)
    (X E : EvertseCubicField) : ℝ :=
  Real.sqrt (max (w X) (w E))

/-- The product of projective sup norms in the normalization where the quadratic field has total place weight one.-/
def evertseGlobalNormalizedProjectiveNorm
    (X E : EvertseCubicField) : ℝ :=
  (∏ w : NumberField.InfinitePlace EvertseCubicField,
      evertseInfiniteProjectiveNorm w X E) *
    ∏ᶠ w : NumberField.FinitePlace EvertseCubicField,
      evertseFiniteProjectiveNorm w X E

/-! ## Normalized scalar norms and projective distances at retained places -/

/-- The scalar norm at a retained place, square-root normalized at finite places.-/
def evertsePlaceScalarNorm
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (a : EvertseCubicField) : ℝ :=
  match v with
  | Sum.inl w => w a
  | Sum.inr w => Real.sqrt (w.1 a)

/-- The normalized projective sup norm of two homogeneous coordinates at a retained place.-/
def evertsePlaceProjectiveNorm
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS) (X E : EvertseCubicField) : ℝ :=
  max (evertsePlaceScalarNorm v X) (evertsePlaceScalarNorm v E)

/-- The normalized projective distance between two homogeneous points at a retained place.-/
def evertsePlaceProjectiveDistance
    {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (v : EvertsePlace S hS)
    (X₁ E₁ X₂ E₂ : EvertseCubicField) : ℝ :=
  evertsePlaceScalarNorm v (X₁ * E₂ - X₂ * E₁) /
    (evertsePlaceProjectiveNorm v X₁ E₁ *
      evertsePlaceProjectiveNorm v X₂ E₂)

/-- Elementary affine comparison used to truncate a projective distance at one.-/
theorem div_max_mul_max_le_two_mul_min
    {a b d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ a + b) :
    d / (max a 1 * max b 1) ≤ 2 * min 1 d := by
  have hA : 1 ≤ max a 1 := le_max_right _ _
  have hB : 1 ≤ max b 1 := le_max_right _ _
  have hden : 0 < max a 1 * max b 1 := mul_pos (by linarith) (by linarith)
  by_cases hd1 : d ≤ 1
  · rw [min_eq_right hd1]
    apply (div_le_iff₀ hden).2
    have hden1 : 1 ≤ max a 1 * max b 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hden1)]
  · have h1d : 1 ≤ d := le_of_lt (lt_of_not_ge hd1)
    rw [min_eq_left h1d]
    apply (div_le_iff₀ hden).2
    have haA : a ≤ max a 1 := le_max_left _ _
    have hbB : b ≤ max b 1 := le_max_left _ _
    have hprod : 0 ≤ (max a 1 - 1) * (max b 1 - 1) :=
      mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
    nlinarith

/-- The six pairwise endpoint products over four real projective norms give the cube of every endpoint norm.-/
theorem evertseFourPair_endpointProduct_real (e : Fin 4 → ℝ) :
    (∏ i : Fin 4, ∏ j ∈ Finset.Ioi i, (e j * e i)) =
      ∏ i : Fin 4, e i ^ 3 := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  rw [hu]
  simp [h0, h1, h2, h3]
  ring

end SUnitQuantitative

end

end RankAmplification
