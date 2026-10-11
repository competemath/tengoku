module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Preliminaries
public import Tengoku.Erdos1196.PrimitiveSetsAboveX.FirstEntryRowTerm
public import Tengoku

/-!
# Core definitions for the normalization constant

This file contains the shared decomposition of the entry weights and normalization constant into
their small-prime and first-entry pieces, together with the structural reindexing lemmas used by
the two separate estimate files.

## Main definitions

* `entryWeightFactor`
* `smallPrimeDivisorSum`
* `firstEntryDivisorSum`
* `normalizationSmallPrimePart`
* `normalizationFirstEntryPart`
-/

@[expose] public section

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/-- The common prefactor `1 / (n log^2 n)` in the entry weights. -/
noncomputable def entryWeightFactor (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)

/-- The small-prime-power divisor sum appearing in `b_x(n)`. -/
noncomputable def smallPrimeDivisorSum (Y n : ℕ) : ℝ :=
  (n.divisors.filter (fun q => q < Y)).sum fun q => Λ q

/-- The first-entry divisor sum appearing in `b_x(n)`. -/
noncomputable def firstEntryDivisorSum (x Y n : ℕ) : ℝ :=
  (n.divisors.filter (fun q => Y ≤ q ∧ n / q < x)).sum fun q => Λ q

/-- The contribution to `b_x(n)` from divisors `q < Y`. -/
noncomputable def smallPrimeEntryWeight (Y n : ℕ) : ℝ :=
  entryWeightFactor n * smallPrimeDivisorSum Y n

/-- The contribution to `b_x(n)` from divisors `q ≥ Y` with `n / q < x`. -/
noncomputable def firstEntryEntryWeight (x Y n : ℕ) : ℝ :=
  entryWeightFactor n * firstEntryDivisorSum x Y n

/-- The small-prime-power summand in the normalization constant `B_x`. -/
noncomputable def normalizationSmallPrimePart (x Y n : ℕ) : ℝ :=
  if x ≤ n then smallPrimeEntryWeight Y n else 0

/-- The first-entry summand in the normalization constant `B_x`. -/
noncomputable def normalizationFirstEntryPart (x Y n : ℕ) : ℝ :=
  if x ≤ n then firstEntryEntryWeight x Y n else 0

/-- `b_x(n)` splits into the small-prime-power and first-entry contributions. -/
lemma entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight (x Y n : ℕ) :
    entryWeight x Y n = smallPrimeEntryWeight Y n + firstEntryEntryWeight x Y n := by
  rw [entryWeight, smallPrimeEntryWeight, firstEntryEntryWeight, entryWeightFactor,
    smallPrimeDivisorSum, firstEntryDivisorSum, mul_add]

/--
Adding the remaining divisor contribution to `b_x(n)` recovers the full weighted divisor sum.
-/
lemma entryWeight_add_filtered_vonMangoldt_eq_entryWeightFactor_sum_divisors (x Y n : ℕ) :
    entryWeight x Y n +
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then entryWeightFactor n * Λ q else 0) =
      entryWeightFactor n * (n.divisors.sum fun q => Λ q) := by
  calc
    entryWeight x Y n +
        n.divisors.sum (fun q =>
          if Y ≤ q ∧ x ≤ n / q then entryWeightFactor n * Λ q else 0)
      = entryWeight x Y n +
          entryWeightFactor n *
            ((n.divisors.filter fun q => Y ≤ q ∧ x ≤ n / q).sum fun q => Λ q) := by
          rw [← Finset.sum_filter, Finset.mul_sum]
    _ 
      = entryWeightFactor n *
          (((n.divisors.filter fun q => q < Y).sum fun q => Λ q) +
            ((n.divisors.filter fun q => Y ≤ q ∧ n / q < x).sum fun q => Λ q) +
            ((n.divisors.filter fun q => Y ≤ q ∧ x ≤ n / q).sum fun q => Λ q)) := by
          simp [entryWeight, entryWeightFactor]
          ring_nf
    _ = entryWeightFactor n * (n.divisors.sum fun q => Λ q) := by
          congr 1
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          calc
            n.divisors.sum (fun q =>
                (if q < Y then Λ q else 0) +
                  (if Y ≤ q ∧ n / q < x then Λ q else 0) +
                    (if Y ≤ q ∧ x ≤ n / q then Λ q else 0))
            _ = n.divisors.sum fun q => Λ q := by
                  refine Finset.sum_congr rfl ?_
                  grind only

/-- The small-prime contribution to `b_x(n)` is nonnegative. -/
lemma smallPrimeEntryWeight_nonneg (Y n : ℕ) : 0 ≤ smallPrimeEntryWeight Y n := by
  unfold smallPrimeEntryWeight entryWeightFactor smallPrimeDivisorSum
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- The first-entry contribution to `b_x(n)` is nonnegative. -/
lemma firstEntryEntryWeight_nonneg (x Y n : ℕ) : 0 ≤ firstEntryEntryWeight x Y n := by
  unfold firstEntryEntryWeight entryWeightFactor firstEntryDivisorSum
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ => ArithmeticFunction.vonMangoldt_nonneg)

/--
The first-entry threshold always lands in the admissible range `x ≤ m * q`, since it dominates the
ceiling quotient `x ⌈/⌉ m`.
-/
lemma le_mul_entryThreshold (x Y m : ℕ) (hm : 0 < m) :
    x ≤ m * entryThreshold x Y m := by
  have hceil : x ≤ m * (x ⌈/⌉ m) := le_smul_ceilDiv hm
  have hle : x ⌈/⌉ m ≤ entryThreshold x Y m := le_max_right _ _
  exact hceil.trans (Nat.mul_le_mul_left _ hle)

/--
The reciprocal sum up to `x - 1` differs from `log x` by at most `1`, which is the `O(1)` input
used in the normalization argument.
-/
private lemma abs_harmonic_pred_sub_log_le_one (x : ℕ) (hx : 1 ≤ x) :
    |(harmonic (x - 1) : ℝ) - Real.log (x : ℝ)| ≤ 1 := by
  by_cases hx1 : x = 1
  · subst hx1
    norm_num [harmonic_zero]
  have hlower : Real.log (x : ℝ) ≤ (harmonic (x - 1) : ℝ) := by
    simpa [Nat.sub_add_cancel hx] using
      (show Real.log (((x - 1) + 1 : ℕ) : ℝ) ≤ (harmonic (x - 1) : ℝ) from
        log_add_one_le_harmonic (x - 1))
  have hupper0 : (harmonic (x - 1) : ℝ) ≤ 1 + Real.log ((x - 1 : ℕ) : ℝ) := by
    exact_mod_cast harmonic_le_one_add_log (x - 1)
  have hlog_mono : Real.log ((x - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < x - 1 by omega)
    · exact_mod_cast Nat.sub_le x 1
  grind only [= abs.eq_1, = max_def]

/-- Equivalently, the finite reciprocal sum `∑_{m < x} 1 / m` is within `1` of `log x`. -/
lemma abs_sum_Icc_inv_sub_log_le_one (x : ℕ) (hx : 1 ≤ x) :
    |(∑ m ∈ Finset.Icc 1 (x - 1), (1 : ℝ) / m) - Real.log (x : ℝ)| ≤ 1 := by
  simpa [one_div, harmonic_eq_sum_Icc] using abs_harmonic_pred_sub_log_le_one x hx

/-- The normalization constant `B_x` is exactly the sum of its small-prime and first-entry
contributions. -/
lemma normalizationConstant_eq_tsum_parts (x Y : ℕ) :
    normalizationConstant x Y =
      ∑' n : ℕ, (normalizationSmallPrimePart x Y n + normalizationFirstEntryPart x Y n) := by
  refine tsum_congr fun n => ?_
  by_cases hn : x ≤ n
  · simp [normalizationSmallPrimePart, normalizationFirstEntryPart, hn,
      entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight]
  · simp [normalizationSmallPrimePart, normalizationFirstEntryPart, hn]

end PrimitiveSetsAboveX
