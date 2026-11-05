module

public import Tengoku.Seed.NumberTheory.Bernoulli
public import Tengoku.Seed.RingTheory.PowerSeries.Log
import Tengoku.KummerCriterion.KummerCriterion.KummerCongruence.BernoulliGeneralized
import Tengoku.KummerCriterion.KummerCriterion.Reflection.ResidueSymbol.DworkFactorization.FiniteArtinHasseFormal
import Tengoku.KummerCriterion.KummerCriterion.Reflection.ResidueSymbol.DworkFactorization.FiniteLogFormal
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.RingTheory.WittVector.IsPoly
import Tengoku.Seed.Tactic.ENatToNat
import Tengoku.Seed.Tactic.NormNum.Irrational
import Tengoku.Seed.Tactic.NormNum.IsCoprime
import Tengoku.Seed.Tactic.NormNum.IsSquare
import Tengoku.Seed.Tactic.NormNum.LegendreSymbol
import Tengoku.Seed.Tactic.NormNum.ModEq
import Tengoku.Seed.Tactic.NormNum.NatFib
import Tengoku.Seed.Tactic.NormNum.NatLog
import Tengoku.Seed.Tactic.NormNum.NatSqrt
import Tengoku.Seed.Tactic.NormNum.Ordinal
import Tengoku.Seed.Tactic.NormNum.Parity
import Tengoku.Seed.Tactic.NormNum.Prime
import Tengoku.Seed.Tactic.NormNum.RealSqrt
import Tengoku.Seed.Tactic.ReduceModChar
import Tengoku.Seed.Data.Nat.Prime.Factorial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Formal Kummer logarithm series

This file starts the purely formal coefficient calculation used by the
cyclotomic-units route. The power-series variable is `T`; the scalar `X`
lives as a polynomial coefficient, so the formal Kummer logarithm is an
element of `ℚ[X]⟦T⟧`.

No analytic `p`-adic logarithm is used here. The only logarithm below is
`PowerSeries.logOf`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators PowerSeries

namespace KummerCriterion
namespace CyclotomicUnits

/-- The ordinary formal exponential numerator `(exp(T)-1)/T`. This is used
as the low-degree model for the Artin-Hasse normalized numerator.-/
def formalExpNormalizedMinusOne : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (PowerSeries.coeff (R := ℚ) (n + 1)) (PowerSeries.exp ℚ)

@[simp]
theorem formalExpNormalizedMinusOne_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n) formalExpNormalizedMinusOne =
      (PowerSeries.coeff (R := ℚ) (n + 1)) (PowerSeries.exp ℚ) := by
  simp [formalExpNormalizedMinusOne]

@[simp]
theorem formalExpNormalizedMinusOne_constantCoeff :
    PowerSeries.constantCoeff formalExpNormalizedMinusOne = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [formalExpNormalizedMinusOne]

theorem exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne :
    PowerSeries.exp ℚ - 1 =
      PowerSeries.X * formalExpNormalizedMinusOne := by
  simpa [formalExpNormalizedMinusOne] using
    (PowerSeries.sub_const_eq_X_mul_shift (PowerSeries.exp ℚ))

theorem bernoulliPowerSeries_mul_formalExpNormalizedMinusOne :
    _root_.bernoulliPowerSeries ℚ * formalExpNormalizedMinusOne = 1 := by
  apply PowerSeries.X_mul_cancel
  calc
    PowerSeries.X * (_root_.bernoulliPowerSeries ℚ * formalExpNormalizedMinusOne)
        = _root_.bernoulliPowerSeries ℚ *
            (PowerSeries.X * formalExpNormalizedMinusOne) := by ring
    _ = _root_.bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) := by
          rw [← exp_sub_one_eq_X_mul_formalExpNormalizedMinusOne]
    _ = PowerSeries.X := by
          rw [_root_.bernoulliPowerSeries_mul_exp_sub_one]
    _ = PowerSeries.X * (1 : PowerSeries ℚ) := by rw [mul_one]

theorem coeff_pow_eq_of_coeff_eq_le
    {A : Type*} [CommSemiring A] {F G : PowerSeries A} :
    ∀ (m d : ℕ), (∀ k, k ≤ d → PowerSeries.coeff k F = PowerSeries.coeff k G) →
      PowerSeries.coeff d (F ^ m) = PowerSeries.coeff d (G ^ m)
  | 0, d, _ => by simp
  | m + 1, d, h => by
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, k⟩ hik
      have hiksum : i + k = d := Finset.mem_antidiagonal.mp hik
      have hi : i ≤ d := by omega
      have hk : k ≤ d := by omega
      change PowerSeries.coeff i (F ^ m) * PowerSeries.coeff k F =
        PowerSeries.coeff i (G ^ m) * PowerSeries.coeff k G
      rw [coeff_pow_eq_of_coeff_eq_le (m := m) (d := i)
          (fun t ht => h t (ht.trans hi)),
        h k hk]

theorem coeff_logOf_eq_of_coeff_eq_le
    {A : Type*} [CommRing A] [Algebra ℚ A] {F G : PowerSeries A} {d : ℕ}
    (hF0 : PowerSeries.constantCoeff F = 1)
    (hG0 : PowerSeries.constantCoeff G = 1)
    (hcoeff : ∀ k, k ≤ d → PowerSeries.coeff k F = PowerSeries.coeff k G) :
    PowerSeries.coeff d (PowerSeries.logOf F) =
      PowerSeries.coeff d (PowerSeries.logOf G) := by
  have hFsub0 : PowerSeries.constantCoeff (F - 1) = 0 := by simp [hF0]
  have hGsub0 : PowerSeries.constantCoeff (G - 1) = 0 := by simp [hG0]
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq]
  rw [Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (F - 1) hFsub0 d,
    Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
      (G - 1) hGsub0 d]
  refine Finset.sum_congr rfl ?_
  intro m hm
  congr 1
  exact coeff_pow_eq_of_coeff_eq_le (m := m) (d := d) fun k hk => by
    simp [hcoeff k hk]

/-- Reduction of a rational number modulo `p`, written using numerator and
denominator. The later coefficient theorems use separate hypotheses proving
that the denominators in question are units modulo `p`.-/
def ratReductionZMod (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  (q.num : ZMod p) / (q.den : ZMod p)

/-- The Bernoulli factor in the final formal congruence, namely the reduction
of `B_(2*j)/(2*j)` modulo `p`.-/
def bernoulliFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  ratReductionZMod p (((_root_.bernoulli (2 * j) : ℚ) / (2 * j : ℚ)))

/-- The explicit unit factor used for the coefficient convention. The
factorial is a unit in the final range `2*j <= p - 3`.-/
def kummerLogUnitFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  -(((Nat.factorial (2 * j) : ℕ) : ZMod p)⁻¹)

theorem factorial_two_mul_index_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (((Nat.factorial (2 * j) : ℕ) : ZMod p)) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ Nat.factorial (2 * j) :=
    (ZMod.natCast_eq_zero_iff (Nat.factorial (2 * j)) p).mp hzero
  have hlt : 2 * j < p := by omega
  exact Nat.not_lt.mpr ((Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)).mp hp_dvd) hlt

theorem kummerLogUnitFactor_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 := by
  simpa [kummerLogUnitFactor] using
    (neg_ne_zero.mpr (inv_ne_zero (factorial_two_mul_index_zmod_ne_zero hj hjp)))

/-- Under the range hypotheses, the integer `2*j` is nonzero modulo
`p`.-/
theorem two_mul_index_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ((2 * j : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ 2 * j :=
    (ZMod.natCast_eq_zero_iff (2 * j) p).mp hzero
  have hpos : 0 < 2 * j := by omega
  have hp_le : p ≤ 2 * j := Nat.le_of_dvd hpos hp_dvd
  omega

/-- Under the range hypotheses, `p` does not divide the denominator of
`B_(2*j)`.-/
theorem prime_not_dvd_bernoulli_den_two_mul {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ¬ p ∣ (_root_.bernoulli (2 * j)).den := by
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    have : 2 * j ≤ 0 := by omega
    omega
  exact KummerCriterion.prime_not_dvd_bernoulli_den_of_lt_sub_one
    (p := p) (n := 2 * j) hp_ne_two (by omega)

/-- Under the range hypotheses, the Bernoulli denominator is nonzero
modulo `p`.-/
theorem bernoulli_den_zmod_ne_zero {p j : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (((_root_.bernoulli (2 * j)).den : ℕ) : ZMod p) ≠ 0 := fun hzero =>
  prime_not_dvd_bernoulli_den_two_mul hj hjp
    ((ZMod.natCast_eq_zero_iff ((_root_.bernoulli (2 * j)).den) p).mp hzero)

/-- The coefficient ring for the final mod-`p` formal Kummer coefficient.-/
abbrev KummerLogModCoeffRing (p : ℕ) : Type :=
  Polynomial (ZMod p)

/-- The reduced scalar multiplying `X^(2*j)-1` in the final mod-`p`
coefficient formula. It is the Bernoulli factor times the factorial unit
coming from the formal logarithm coefficient convention.-/
def reducedKummerLogCoeffFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  kummerLogUnitFactor p j * bernoulliFactor p j

/-- The final mod-`p` formal coefficient polynomial.-/
def formalKummerLogCoeffModP (p j : ℕ) [Fact p.Prime] :
    KummerLogModCoeffRing p :=
  Polynomial.C (reducedKummerLogCoeffFactor p j) *
    (Polynomial.X ^ (2 * j) - 1)

/-- The unit factor in the final unspecialized theorem is nonzero.-/
theorem formalKummerLogCoeffModP_unit_ne_zero
    {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    kummerLogUnitFactor p j ≠ 0 :=
  kummerLogUnitFactor_ne_zero hj hjp

/-- Evaluation of the final mod-`p` formal coefficient polynomial.-/
theorem formalKummerLogCoeffModP_eval
    (p j : ℕ) [Fact p.Prime] (x : ZMod p) :
    Polynomial.eval x (formalKummerLogCoeffModP p j) =
      (kummerLogUnitFactor p j * bernoulliFactor p j) *
        (x ^ (2 * j) - 1) := by
  simp [formalKummerLogCoeffModP, reducedKummerLogCoeffFactor]

end CyclotomicUnits
end KummerCriterion

end
