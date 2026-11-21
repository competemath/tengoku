import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.EinsteinBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.PositiveEinstein

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.Euler

noncomputable def killingDerivativeCoeff (r : RawGraph)
    (i a k : I6) : ℝ :=
  ∑ j, r.inverseTranspose j a *
    (r.gamma i j k + r.bracketCoeff j i k)

noncomputable def killingEnergy (r : RawGraph) : ℝ :=
  ∑ i, ∑ a, ∑ k, killingDerivativeCoeff r i a k ^ 2

noncomputable def backgroundRicciTrace (r : RawGraph) : ℝ :=
  ∑ a, ∑ j, ∑ k,
    r.inverseTranspose j a * r.inverseTranspose k a * r.ricciCoeff j k

noncomputable def backgroundNorm (r : RawGraph) : ℝ :=
  ∑ a, ∑ j, r.inverseTranspose j a ^ 2

end S3xS3.Trivial.PositiveEinstein
