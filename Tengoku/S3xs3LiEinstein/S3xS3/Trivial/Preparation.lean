import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.IsotropyGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Preparation

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.PositiveEinstein
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.Normalize
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.IsotropyGeometry
open S3xS3.Trivial.Support

structure PreparedEinstein (g : LeftInvariantMetric) where
  action : InnerAction
  graph : GraphData (pullbackMetric action g)
  euler : EulerData
  P_eq : euler.P = graph.P
  Q_eq : euler.Q = graph.Q
  M_eq : euler.M = graph.M

end S3xS3.Trivial.Preparation
