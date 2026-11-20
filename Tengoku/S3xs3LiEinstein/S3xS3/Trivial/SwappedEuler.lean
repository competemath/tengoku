import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.FactorSwapFormulas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SwappedEuler

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.PositiveEinstein
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.Preparation
open S3xS3.Trivial.FactorSwap
open S3xS3.Trivial.FactorSwapFormulas
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.IsotropyGeometry

structure EulerForGraph {g : LeftInvariantMetric} (d : GraphData g)
    (lambda : ℝ) where
  U : SO3
  V : SO3
  euler : EulerData
  P_eq : euler.P = (d.pullback U V).P
  Q_eq : euler.Q = (d.pullback U V).Q
  M_eq : euler.M = (d.pullback U V).M
  kappa_eq : euler.kappa = 2 * lambda

end S3xS3.Trivial.SwappedEuler
