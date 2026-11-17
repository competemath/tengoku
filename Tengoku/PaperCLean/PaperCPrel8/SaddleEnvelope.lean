import Tengoku.PaperCLean.PaperCV282.SaddleAsymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The convex saddle envelope with second-scale error

The tangent inequality is proved on the actual upper saddle branch by
monotonicity in its parameter. No inverse-function differentiability or
second derivative of the inverse branch is assumed.
-/
namespace PaperC.Prel8.SaddleEnvelope
open PaperC.V282.SaddleBranch PaperC.V282.SaddleParameters
open PaperC.V282.ExponentialIntegral PaperC.V282.SaddleAsymptotics
open Set Filter Topology
noncomputable section

/-- Explicit error measured in units of the paper's second scale.-/
def relativeEnvelopeError (u : ℝ) : ℝ :=
  normalizedExponentialIntegral u ^ 2 / (u*saddleCostFactor u)

end
end PaperC.Prel8.SaddleEnvelope
