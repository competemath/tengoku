import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.CauchyEvaluation

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_116 u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128 u_129 u_130 u_131 u_132 u_133 u_134 u_135 u_136 u_137 u_138 u_139 u_140 u_141 u_142 u_143 u_144 u_145 u_146 u_147 u_148 u_149 u_150 u_151 u_152 u_153

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
section

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_121} [Fintype n] [DecidableEq n]

open scoped Kronecker

variable {m : Type u_122} [Fintype m] [DecidableEq m]

open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_123} [Fintype n] [DecidableEq n]

open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_124} [Fintype n] [DecidableEq n]

open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_125} {m : Type u_126} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real
section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology
section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_150} {m : Type u_151} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def boundaryDiskDensity (D : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (1-z⁻¹ • D)⁻¹ + ((1-z⁻¹ • D)⁻¹)ᴴ - 1

lemma coordinate_circle_cauchy {ψ H : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
      (ψ (t.toCircle : ℂ)-z))*H (ψ (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = H z := by
  apply circle_convex_cauchy (convex_closedBall (0:ℂ) 1) hH hψ
    (fun t ht => by simpa [mem_closedBall] using (hb t ht).le)
    (ball_subset_closedBall hz) _ (hmass z hz)
  intro t ht he
  have hh := hb t ht
  rw [he] at hh
  have hz' : ‖z‖ < 1 := by simpa using hz
  exact (ne_of_lt hz') hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_152} {m : Type u_153} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma coordinate_circle_cauchy_matrix {ψ : ℂ → ℂ} {J : ℂ → Matrix n n ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hJ : ∀ i j, AnalyticOnNhd ℂ (fun z => J z i j) (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        J (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = J 0 := by
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hψc := hψ.continuousOn.comp_continuous hc ht
  have hψd := hψ.deriv.continuousOn.comp_continuous hc ht
  have hjc : Continuous (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) :=
    (hc.mul hψd).div hψc (fun t => norm_ne_zero_iff.mp (by rw [hb _ (ht t)]; norm_num))
  have hJc : Continuous (fun t : UnitAddCircle => J (ψ (t.toCircle : ℂ))) := by
    apply continuous_matrix
    intro i j
    exact (hJ i j).continuousOn.comp_continuous hψc
      (fun t => by simpa [mem_closedBall] using (hb _ (ht t)).le)
  have hi := (hjc.smul hJc).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  ext i j
  erw [matrix_integral_entry hi]
  convert! coordinate_circle_cauchy hψ hb (hJ i j) hmass (z := 0) (by simp) using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ) *
      J (ψ (t.toCircle : ℂ)) i j =
    (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/(ψ (t.toCircle : ℂ)-0) *
      J (ψ (t.toCircle : ℂ)) i j
  rw [sub_zero]

end CompleteCrouzeix

end

end OAI
