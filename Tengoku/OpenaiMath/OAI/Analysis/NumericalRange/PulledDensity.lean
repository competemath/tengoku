import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.BoundaryRepresentation

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_154 u_155 u_156

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_154} [Fintype n] [DecidableEq n]

def pulledDiskDensity (D : Matrix n n ℂ) (ψ : ℂ → ℂ) (t : UnitAddCircle) : Matrix n n ℂ :=
  (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ))) •
    boundaryDiskDensity D (ψ (t.toCircle : ℂ))

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_155} {m : Type u_156} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

end CompleteCrouzeix

end

end OAI
