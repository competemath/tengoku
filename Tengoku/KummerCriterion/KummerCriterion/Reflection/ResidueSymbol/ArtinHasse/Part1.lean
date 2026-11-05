module

public import Tengoku.KummerCriterion.KummerCriterion.Reflection.ResidueSymbol.DieudonneDwork.Part1
public import Tengoku.Seed.RingTheory.PowerSeries.Exp
import Tengoku.KummerCriterion.KummerCriterion.Reflection.ResidueSymbol.DieudonneDwork.Part2
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.CategoryTheory.Category.Init
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Artin-Hasse exponential power series

This file defines the Artin-Hasse log and exponential power series over `ℚ`,
indexed by a prime `r`:

* `artinHasseLogSeries r: PowerSeries ℚ` is `L_r(T) = ∑_{i ≥ 0} T^{r^i} / r^i`.
* `artinHasseExpSeries r: PowerSeries ℚ` is `E_r(T) = exp(L_r(T))`.

The "is a power of `r`" predicate is decidable via `Nat.log`: for `r ≥ 2`,
`n = r^i` for some `i ≥ 0` iff `r ^ Nat.log r n = n ∧ n ≠ 0`. (For `n = 0`,
`r ^ Nat.log r 0 = r ^ 0 = 1 ≠ 0`, so the predicate fails as expected.)

These are the building blocks of the Dwork coefficient sequence used by the
`FullTeichDworkSetup` interface in (the project's Φ/Kelly/Furtwängler
route). p-integrality of the Artin-Hasse exponential coefficients (the
substantive Dieudonné-Dwork content) is proved separately.

## References

* Alain M. Robert, *A Course in p-adic Analysis* (GTM 198, Springer 2000),
 §7.1 Definition 1, p. 187.
* Neal Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*
 (GTM 58, Springer 1984), §IV.2 Definition, p. 93.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

namespace Furtwaengler

universe u v w

/-- The Artin-Hasse "log" series at prime `r`:
`L_r(T):= ∑_{i ≥ 0} T^{r^i} / r^i ∈ ℚ[[T]]`.

Coefficient `[T^n] L_r(T)` is `1 / r^(Nat.log r n)` if `n = r^(Nat.log r n)`
and `n ≠ 0` (i.e., if `n` is a positive power of `r`), else `0`.
The constant coefficient is `0` because `0` is excluded explicitly.-/
noncomputable def artinHasseLogSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if r ^ Nat.log r n = n ∧ n ≠ 0 then
      (1 : ℚ) / (r : ℚ) ^ Nat.log r n
    else 0

/--
@isnad1 id=eq.0h2v.s7.086b3d41c6e1 from=translated src=- shape=8a1ae537 vocab=a53c9395
-/
@[simp] theorem artinHasseLogSeries_coeff (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseLogSeries r) =
      if r ^ Nat.log r n = n ∧ n ≠ 0 then
        (1 : ℚ) / (r : ℚ) ^ Nat.log r n
      else 0 := by
  unfold artinHasseLogSeries
  exact PowerSeries.coeff_mk n _

/--
@isnad1 id=eq.0h1v.s5.154f11b8b8a8 from=translated src=- shape=c29e1501 vocab=1fafdf55
-/
@[simp] theorem artinHasseLogSeries_constantCoeff (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.constantCoeff (R := ℚ)) (artinHasseLogSeries r) = 0 := by
  unfold artinHasseLogSeries
  rw [PowerSeries.constantCoeff_mk]
  simp

/--
@isnad1 id=hassubst.0h1v.s3.d5af9d17cfe0 from=translated src=- shape=47ccca8d vocab=8d6fb9e0
-/
theorem artinHasseLogSeries_hasSubst (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries.HasSubst (artinHasseLogSeries r) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (artinHasseLogSeries_constantCoeff r)

/-- The Artin-Hasse exponential at prime `r`:
`E_r(T):= exp(L_r(T)) ∈ ℚ[[T]]`.

Defined via formal power-series substitution of `L_r(T)` into the universal
exponential series. The substitution is well-defined because
`L_r(T)` has zero constant coefficient (`artinHasseLogSeries_constantCoeff`).-/
noncomputable def artinHasseExpSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  PowerSeries.subst (artinHasseLogSeries r) (PowerSeries.exp ℚ)

private theorem artinHasseLogSeries_coeff_eq_X_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseLogSeries r) =
      (PowerSeries.coeff (R := ℚ) n) (PowerSeries.X : PowerSeries ℚ) := by
  have hr_prime : Nat.Prime r := Fact.out
  have hr_pos : 0 < r := hr_prime.pos
  rw [artinHasseLogSeries_coeff, PowerSeries.coeff_X]
  by_cases hn1 : n = 1
  · subst n
    simp [Nat.log_one_right]
  · have hnot :
        ¬ (r ^ Nat.log r n = n ∧ n ≠ 0) := by
      rintro ⟨hlog, _hn0⟩
      have hlog_zero : Nat.log r n = 0 := by
        cases hlogn : Nat.log r n with
        | zero => rfl
        | succ m =>
            have hr_le_pow : r ≤ r ^ (m + 1) := by
              rw [pow_succ']
              exact Nat.le_mul_of_pos_right r (pow_pos hr_pos m)
            have hr_le_n : r ≤ n := by
              rw [← hlog, hlogn]
              exact hr_le_pow
            exact False.elim ((not_lt_of_ge hr_le_n) hn)
      have hn_eq_one : n = 1 := by
        rw [← hlog, hlog_zero]
        simp
      exact hn1 hn_eq_one
    rw [ite_eq_right hnot, ite_eq_right hn1]

private theorem artinHasseLogSeries_trunc_eq_X
    (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries.trunc r (artinHasseLogSeries r) =
      PowerSeries.trunc r (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hn : n < r
  · rw [ite_eq_left hn, ite_eq_left hn, artinHasseLogSeries_coeff_eq_X_of_lt r hn]
  · rw [ite_eq_right hn, ite_eq_right hn]

private theorem artinHasseLogSeries_pow_coeff_eq_X_pow_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] (d : ℕ) {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) ((artinHasseLogSeries r) ^ d) =
      (PowerSeries.coeff (R := ℚ) n) ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
  have htrunc := artinHasseLogSeries_trunc_eq_X r
  have hpow :
      PowerSeries.trunc r ((artinHasseLogSeries r) ^ d) =
        PowerSeries.trunc r ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
    rw [← PowerSeries.trunc_trunc_pow (artinHasseLogSeries r) r d,
      ← PowerSeries.trunc_trunc_pow (PowerSeries.X : PowerSeries ℚ) r d,
      htrunc]
  have hcoeff := congrArg (fun P : Polynomial ℚ => P.coeff n) hpow
  simpa [PowerSeries.coeff_trunc, hn] using hcoeff

private theorem artinHasseExpSeries_coeff_eq_exp_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries r) =
      (PowerSeries.coeff (R := ℚ) n) (PowerSeries.exp ℚ) := by
  unfold artinHasseExpSeries
  calc
    (PowerSeries.coeff (R := ℚ) n)
        (PowerSeries.subst (artinHasseLogSeries r) (PowerSeries.exp ℚ)) =
        (PowerSeries.coeff (R := ℚ) n)
          (PowerSeries.subst (PowerSeries.X : PowerSeries ℚ) (PowerSeries.exp ℚ)) := by
      rw [PowerSeries.coeff_subst' (artinHasseLogSeries_hasSubst r),
        PowerSeries.coeff_subst' (PowerSeries.HasSubst.X' (R := ℚ))]
      apply finsum_congr
      intro d
      rw [artinHasseLogSeries_pow_coeff_eq_X_pow_of_lt r d hn]
    _ = (PowerSeries.coeff (R := ℚ) n) (PowerSeries.exp ℚ) := by
      rw [PowerSeries.X_subst]

/-- Below degree `r`, the Artin-Hasse exponential has the same coefficients as
the ordinary exponential.
@isnad1 id=eq.1h2v.s6.671c9e44e788 from=translated src=- shape=f7881435 vocab=18711ee6
-/
theorem artinHasseExpSeries_coeff_eq_inv_factorial_of_lt
    (r : ℕ) [Fact (Nat.Prime r)] {n : ℕ} (hn : n < r) :
    (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries r) =
      (1 : ℚ) / (Nat.factorial n : ℚ) := by
  rw [artinHasseExpSeries_coeff_eq_exp_of_lt r hn]
  simp

/-- The series `E_r(T) - 1`, whose compositional inverse is the formal source
of the corrected Dwork parameter.-/
noncomputable def artinHasseExpMinusOneSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  artinHasseExpSeries r - 1

/--
@isnad1 id=eq.0h1v.s6.95c861008d7c from=translated src=- shape=6654d5d3 vocab=01ea7036
-/
@[simp] theorem artinHasseExpMinusOneSeries_coeff_one
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpMinusOneSeries r) = 1 := by
  have hr : 1 < r := (Fact.out : Nat.Prime r).one_lt
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpSeries r) = 1 := by
    simpa using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt r hr
  simp [artinHasseExpMinusOneSeries, hcoeff]

/-- The compositional inverse of `E_r(T) - 1`. Evaluating this at
`ζ_r - 1` in a suitable complete local ring is the formal construction of the
corrected Dwork parameter.-/
noncomputable def artinHasseExpInverseSeries (r : ℕ) [Fact (Nat.Prime r)] :
    PowerSeries ℚ :=
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  PowerSeries.substInv P

/--
@isnad1 id=eq.0h1v.s5.372c079496f4 from=translated src=- shape=c29e1501 vocab=b7e717cf
-/
@[simp] theorem artinHasseExpInverseSeries_constantCoeff
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.constantCoeff (R := ℚ)) (artinHasseExpInverseSeries r) = 0 := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  simp [artinHasseExpInverseSeries]

/--
@isnad1 id=eq.0h1v.s6.49e70525ab0d from=translated src=- shape=6654d5d3 vocab=23d6193a
-/
@[simp] theorem artinHasseExpInverseSeries_coeff_one
    (r : ℕ) [Fact (Nat.Prime r)] :
    (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpInverseSeries r) = 1 := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  simp [artinHasseExpInverseSeries, P, hcoeff]

end Furtwaengler

end KummerCriterion

end
