import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The normalized scalar Stieltjes characterization

Existence, uniqueness, exact mass, and compact support are derived from
holomorphy, positivity, high-imaginary normalization, and the exterior
imaginary estimate. This is the scalar measure-theoretic input to the
matrix Dyson representation, Ajanki--Erdos--Kruger, Proposition 2.1.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
