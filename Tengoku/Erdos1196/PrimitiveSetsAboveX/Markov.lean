module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Normalization
public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Preliminaries

/-!
# Markov-chain lemmas for primitive sets above `x`

This file proves the main analytic estimates for the Markov-chain construction: the asymptotic
control of `R_Y(m)`, the eventual sub-Markov bound on the transition rows, the eventual estimate
for the normalization constant `B_x`, and the explicit closed formula for the visiting
probabilities.

## Main statements

* `subMarkovRowSumBound`
* `normalizationEstimate`
* `visitProbabilityFormula`
-/

@[expose] public section

/- ! Markov-chain identities and row-sum bounds used in the proof. -/
open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- If a summand vanishes off the divisors of `n`, its infinite sum is the finite sum over
`n.divisors`. -/
lemma tsum_eq_sum_divisors_of_nondivisors_zero {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {n : ℕ} (hn : 0 < n) (f : ℕ → α) (hf : ∀ q, ¬ q ∣ n → f q = 0) :
    (∑' q : ℕ, f q) = n.divisors.sum f := by
  refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := n.divisors) ?_
  intro q hq
  exact hf q (by grind only [= Nat.mem_divisors])

/-- If a divisor condition is bundled into the summand, the `tsum` reduces to the finite divisor
sum with that condition removed. -/
lemma tsum_eq_sum_divisors_of_dvd_and {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {n : ℕ} (hn : 0 < n) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → α) :
    (∑' q : ℕ, if q ∣ n ∧ P q then f q else 0) =
      n.divisors.sum (fun q => if P q then f q else 0) := by
  calc
    (∑' q : ℕ, if q ∣ n ∧ P q then f q else 0) =
        n.divisors.sum (fun q => if q ∣ n ∧ P q then f q else 0) := by
          refine tsum_eq_sum_divisors_of_nondivisors_zero (n := n) hn _ ?_
          intro q hq
          simp [hq]
    _ = n.divisors.sum (fun q => if P q then f q else 0) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          grind only [= Nat.mem_divisors]

/--
For a proper parent `n / q`, any last-jump term with the explicit parent value simplifies to the
common factor `(1 / B_x) * (Λ(q) / (n log^2 n))`.
-/
lemma lastJumpContribution_eq_of_formula {x Y : ℕ} (hx : 2 ≤ x) {n q : ℕ}
    (hq : q ∈ n.divisors) (hqx : Y ≤ q ∧ x ≤ n / q) {v : ℝ}
    (hvisit :
      v = 1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) :
    v * transitionWeight Y (n / q) q =
      (1 / normalizationConstant x Y) *
        ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q) := by
  rcases hqx with ⟨hYq, hxq⟩
  have hdvd : q ∣ n := Nat.dvd_of_mem_divisors hq
  have hq_pos : 0 < q := Nat.pos_of_mem_divisors hq
  have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
    Nat.cast_div hdvd (by exact_mod_cast hq_pos.ne')
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hlog_ne : Real.log ((n : ℝ) / q) ≠ 0 := by
    rw [← hcast_div]
    have hnq2 : 2 ≤ n / q := le_trans hx hxq
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hnq2))).ne'
  rw [hvisit, transitionWeight, ite_eq_left hYq, hcast_div]
  calc
    (1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) *
        ((Real.log ((n : ℝ) / q) / (Real.log (((n / q) * q : ℕ) : ℝ)) ^ 2) *
          (Λ q / (q : ℝ))) =
        (1 / normalizationConstant x Y) *
          ((1 / (((n : ℝ) / q) * Real.log ((n : ℝ) / q))) *
            ((Real.log ((n : ℝ) / q) / (Real.log (n : ℝ)) ^ 2) *
              (Λ q / (q : ℝ)))) := by
          grind only [Nat.div_mul_cancel hdvd]
    _ = (1 / normalizationConstant x Y) *
          ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q) := by
          congr 1
          field_simp [hlog_ne, hqR]

/--
The divisor decomposition of `log n` rewrites the explicit target formula as the normalized initial
mass plus the filtered von Mangoldt divisor sum.
-/
lemma formula_eq_initialDistribution_add_filteredVonMangoldt {x Y n : ℕ} :
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
      initialDistribution x Y n +
        (1 / normalizationConstant x Y) *
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
            else 0) := by
  calc
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
        (1 / normalizationConstant x Y) *
          ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) *
            (n.divisors.sum fun q => Λ q)) := by
          rw [ArithmeticFunction.vonMangoldt_sum (n := n)]
          grind only
    _ = (1 / normalizationConstant x Y) *
          (entryWeight x Y n +
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0)) := by
          congr 1
          simpa [entryWeightFactor] using
            (entryWeight_add_filtered_vonMangoldt_eq_entryWeightFactor_sum_divisors x Y n).symm
    _ = initialDistribution x Y n +
          (1 / normalizationConstant x Y) *
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0) := by
          simp [initialDistribution, div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm]

/--
If every last-jump parent already has the explicit value `1 / (B_x n log n)`, then the recurrence
right-hand side collapses to the closed formula for the visit probability at `n`.
-/
lemma explicitFormula_eq_recurrence_rhs {x Y n : ℕ} (hx : 2 ≤ x) (hn : x ≤ n) {f : ℕ → ℝ}
    (hvisit :
      ∀ ⦃q : ℕ⦄, q ∈ n.divisors → Y ≤ q ∧ x ≤ n / q → q ≠ 1 →
        f (n / q) =
          1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) :
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
      initialDistribution x Y n +
        ∑' q : ℕ,
          if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
            f (n / q) * transitionWeight Y (n / q) q
          else 0 := by
  have hn_pos : 0 < n := by omega
  have hrec :
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then
          f (n / q) * transitionWeight Y (n / q) q
        else 0) =
        (1 / normalizationConstant x Y) *
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
            else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro q hq
    by_cases hqx : Y ≤ q ∧ x ≤ n / q
    · by_cases hq1 : q = 1
      · subst hq1
        simp [transitionWeight, hqx]
      · simpa [hqx] using
          (lastJumpContribution_eq_of_formula (x := x) (Y := Y) (n := n) (q := q)
            hx hq hqx (v := f (n / q)) (hvisit hq hqx hq1))
    · simp [hqx]
  calc
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
        initialDistribution x Y n +
          (1 / normalizationConstant x Y) *
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0) := by
            simpa using
              formula_eq_initialDistribution_add_filteredVonMangoldt (x := x) (Y := Y) (n := n)
    _ = initialDistribution x Y n +
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              f (n / q) * transitionWeight Y (n / q) q
            else 0) := by
          rw [hrec]
    _ = initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              f (n / q) * transitionWeight Y (n / q) q
            else 0 := by
          congr 1
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and (n := n) hn_pos
              (P := fun q => Y ≤ q ∧ x ≤ n / q)
              (fun q => f (n / q) * transitionWeight Y (n / q) q)).symm

/--
The Markov layer visits each state `n ≥ x` with the explicit probability
`1 / (B_x n log n)`. The lower bound `2 ≤ x` guarantees that the logarithms in this formula are
positive.
-/
lemma visitProbabilityFormula {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x) {n : ℕ}
    (hn : x ≤ n) :
    chain.visitProbability n =
      1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  rw [chain.visitProbabilityRecurrence (n := n) hn]
  symm
  refine explicitFormula_eq_recurrence_rhs (x := x) (Y := Y) (n := n) hx hn
    (f := chain.visitProbability) ?_
  intro q hq hqx hq1
  have hn_pos : 0 < n := by omega
  have hq_ne_zero : q ≠ 0 := (Nat.pos_of_mem_divisors hq).ne'
  have hlt : n / q < n := by
    have hq_gt_one : 1 < q := by omega
    exact Nat.div_lt_self hn_pos hq_gt_one
  have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
    Nat.cast_div (Nat.dvd_of_mem_divisors hq) (by exact_mod_cast hq_ne_zero)
  simpa [hcast_div] using ih (n / q) hlt hqx.2

/-- Under the standing hypotheses `2 ≤ x` and `B_x > 0`, the visiting probabilities are
nonnegative on the state space `n ≥ x`. -/
lemma visitProbability_nonneg {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x)
    (hB : 0 < normalizationConstant x Y) {n : ℕ} (hn : x ≤ n) :
    0 ≤ chain.visitProbability n := by
  rw [visitProbabilityFormula chain hx hn]
  positivity

end PrimitiveSetsAboveX
