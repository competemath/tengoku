module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.CountFibre
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.CountPartition
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.Uniform

/-!
# Capped marked Poisson prefix identities

Finite Poisson count mixtures from a fixed iid sample agree with the
nonoverflow restriction of the marked Poisson finite-prefix law.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- For [an iid marked observation law](hyp:ν), [a Poisson mean](hyp:lam),
[a count cap](hyp:n), [a finite-sample statistic](hyp:g), and [an integrability condition](hyp:hg),
[the finite Poisson count mixture
of admissible prefixes equals its nonoverflow finite Poisson expectation](goal). -/
theorem poisson_prefix_mixture_integral
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0) (n : ℕ)
    (g : FiniteSample Y → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw ν lam)) :
    (∑ M : Fin (n + 1),
      (poissonMeasure lam {M.val}).toReal *
        ∫ y : Fin n → Y,
          g (prefixOfLE y M.val (Nat.le_of_lt_succ M.isLt))
          ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ z : FiniteSample Y,
        if z.count ≤ n then g z else 0
        ∂finitePoissonSampleLaw ν lam := by
  /- Apply `poisson_nonoverflow_integral_eq_sum_count_fibres` on the right,
  then rewrite each count fibre with `poisson_prefix_count_fibre_integral`.
  The latter already handles zero-Poisson-mass fibres. -/
  rw [poisson_nonoverflow_integral_eq_sum_count_fibres ν lam n g hg]
  congr 1
  funext M
  exact (poisson_prefix_count_fibre_integral ν lam n M.val
    (Nat.le_of_lt_succ M.isLt) g hg).symm

end Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
