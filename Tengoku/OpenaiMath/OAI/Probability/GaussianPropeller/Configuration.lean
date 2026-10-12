import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.FourCells

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

structure Configuration (d k:ℕ) where
  z : Fin k→Space d
  P : Fin k→ℝ
  zero : ∑ j,z j=0
  norm : ∑ j,‖z j‖^2=1
  pos : ∀ j,z j≠0
  order : Antitone (fun j=>‖z j‖)
  obtuse : Pairwise (fun j l=>⟪z j,z l⟫<0)
  cap : ∀ j,‖z j‖≤2/3
  probability : ∑ j,P j=1
  half : ∀ j,P j≤1/2
  quadratic : ∀ j,(if k=5 then (0.929:ℝ) else 0.884)*‖z j‖^2≤P j
  linear : ∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j
  pair : ∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2
  cap3 : k=4 → ∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j)
  loss4 : k=4 → ∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x

variable {d k:ℕ} [NeZero k]

end GaussianPropeller.Reduction

end OAI
