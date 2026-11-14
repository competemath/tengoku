import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductCoefficients
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite positive sums for the quadratic product

These are actual finite Dirichlet sums of the proved convolution coefficients.
The lower bound one holds on either side of the line of absolute convergence;
no identification with an infinite series below that line is made.
-/

noncomputable section

open Finset
open scoped ComplexOrder

namespace TwinPrime.Analytic

def quadraticProductRealPartialSum {q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ q)
    (σ : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 X, (n : ℝ) ^ (-σ) * (quadraticProductCoefficients χ₁ χ₂ n).re

def quadraticProductDirichletPartialSum {q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ q)
    (s : ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 X, (n : ℂ) ^ (-s) * quadraticProductCoefficients χ₁ χ₂ n

end TwinPrime.Analytic
