import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.ChebyshevBoundedVariation
import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries
import Tengoku.Nlalib.NLAlib.Polynomial.Interpolation.ChebyshevSeriesInterpolation
import Tengoku.Nlalib.NLAlib.Polynomial.BestApproximation.MinimaxError
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.DescendingFactorialSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiable Chebyshev approximation

The exact BV coefficient envelope has a telescoping tail. It gives the
truncation, interpolation, and minimax bounds of ATAP Theorem 7.2.
Atlas: `chebyshev-approx-differentiable`.
-/

noncomputable section

open Real Set MeasureTheory Filter Polynomial

namespace NLAlib

end NLAlib
