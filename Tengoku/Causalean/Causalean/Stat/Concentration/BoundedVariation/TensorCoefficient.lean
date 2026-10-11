module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevOneNorm
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Approximation.Chebyshev.EquispacedLagrange
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorGridWeights
public import Tengoku.Causalean.Causalean.Stat.Concentration.BoundedVariation.TensorChebyshev
public import Tengoku.Causalean.Causalean.Stat.Concentration.BoundedVariation.Variation
public import Tengoku.Causalean.Causalean.Stat.Concentration.BoundedVariation.WeightedIntegral

/-!
# Bounded-variation tensor coefficient paths

For a continuous family of bounded-degree tensor polynomials, each fixed monomial coefficient is
a continuous path. A uniform bounded-variation envelope for polynomial values on the normalized
cube transfers to the coefficient paths with an explicit exponential degree cost.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Stat.Concentration.BoundedVariation
open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The coefficient path](goal) of [a time-indexed family of polynomials in
d variables](hyp:p) [whose degree in each variable is at most D](hyp:hdeg)
and [whose values at every point of the integer grid {0, …, D}^d vary
continuously in time](hyp:hgrid), at [a monomial index a](hyp:a), is the
continuous real path on the unit time interval recording the coefficient of
that monomial at each time.

The coefficient of a continuously varying bounded-degree tensor polynomial, packaged as a
continuous real path on the unit threshold interval.
-/
def tensorCoefficientPath {d D : ℕ} (p : Time → MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ D)
    (hgrid : ∀ a : Fin d → Fin (D + 1),
      Continuous (fun t => MvPolynomial.eval (fun i => (a i : ℝ)) (p t)))
    (a : Fin d → Fin (D + 1)) : Path :=
  ⟨fun t => tensorCoeffs (D := D) (p t) a,
    continuous_tensorCoeffs_of_grid p hdeg hgrid a⟩

/-- Every coefficient of a four-variable polynomial of coordinatewise degree `2(K-1)` is a
fixed weighted sum of its values at one finite tensor grid inside the normalized cube. The
total absolute weight over all coefficients and grid points has an exponential degree bound.

One route uses Lagrange nodes `j/(D+1)` with `D = 2(K-1)`. The coefficient one-norm of the
univariate basis polynomial at node `j` is at most
`2^D * (D+1)^D / (j! * (D-j)!)`. Summing over `j` gives
`4^D * (D+1)^D / D!`; the exponential-series bound controls the factorial ratio. Tensor the
four univariate formulas and compare their total weight with `2^(40K+19)`. This is a
quantitative finite-dimensional representation, independent of any time-indexed path. -/
theorem tensorCoeffs_four_cube_weights {K : ℕ} (hK : 0 < K) :
    ∃ (x : (Fin 4 → Fin (2 * (K - 1) + 1)) → Fin 4 → ℝ)
      (w : (Fin 4 → Fin (2 * (K - 1) + 1)) →
        (Fin 4 → Fin (2 * (K - 1) + 1)) → ℝ),
      (∀ b, x b ∈ normalizedCube 4) ∧
      (∀ (p : MvPolynomial (Fin 4) ℝ),
        (∀ i, p.degreeOf i ≤ 2 * (K - 1)) →
        ∀ a, tensorCoeffs (D := 2 * (K - 1)) p a =
          ∑ b, w a b * MvPolynomial.eval (x b) p) ∧
      (∑ a, ∑ b, |w a b|) ≤ (2 : ℝ) ^ (40 * K + 19) := by
  refine ⟨tensorGridPoint, tensorGridWeight, tensorGridPoint_mem_cube, ?_, ?_⟩
  · intro p hdeg a
    exact tensorGrid_coeff_recovery p hdeg a
  · calc
      (∑ a : Fin 4 → Fin (2 * (K - 1) + 1),
          ∑ b : Fin 4 → Fin (2 * (K - 1) + 1),
            |tensorGridWeight a b|) ≤
          ((2 : ℝ) ^ (4 * (2 * (K - 1)) + 4)) ^ 4 :=
        tensorGrid_weight_oneNorm_le 4 (2 * (K - 1))
      _ = (2 : ℝ) ^ (4 * (4 * (2 * (K - 1)) + 4)) := by
        rw [show 4 * (4 * (2 * (K - 1)) + 4) =
          (4 * (2 * (K - 1)) + 4) * 4 by omega, pow_mul]
      _ ≤ (2 : ℝ) ^ (40 * K + 19) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega

end Causalean.Stat.Concentration.BoundedVariation
