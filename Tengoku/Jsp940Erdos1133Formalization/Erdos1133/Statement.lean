import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Inverse
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
import Tengoku.Seed.Topology.Order.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Filter Set
open scoped BigOperators

namespace Erdos1133

/-- A bounded polynomial on the actual interval, not on its sample nodes.-/
def BoundedOnSegment (C : ℝ) (P : Polynomial ℝ) : Prop :=
  ∀ z ∈ Icc (-1 : ℝ) 1, |P.eval z| ≤ C

/-- Angular coordinate in the bandwidth-normalized interval `[0,D]`.-/
def angularNode (D : ℝ) (x : Icc (-1 : ℝ) 1) : ℝ :=
  D / Real.pi * Real.arccos (x : ℝ)

/--
@isnad1 id=mem.1h2v.s5.2339eae4cf78 from=translated src=- shape=217de7d2 vocab=68aaeef9
-/
theorem angularNode_mem {D : ℝ} (hD : 0 ≤ D) (x : Icc (-1 : ℝ) 1) :
    angularNode D x ∈ Icc 0 D := by
  constructor
  · exact mul_nonneg (div_nonneg hD Real.pi_pos.le) (Real.arccos_nonneg _)
  · calc
      angularNode D x ≤ D / Real.pi * Real.pi :=
        mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) (div_nonneg hD Real.pi_pos.le)
      _ = D := by field_simp

/--
@isnad1 id=eq.1h2v.s6.04a1c73f06e9 from=translated src=- shape=0b50aa16 vocab=f55e5566
-/
theorem cos_angularNode {D : ℝ} (hD : 0 < D) (x : Icc (-1 : ℝ) 1) :
    Real.cos (Real.pi / D * angularNode D x) = (x : ℝ) := by
  have he : Real.pi / D * angularNode D x = Real.arccos (x : ℝ) := by
    dsimp [angularNode]
    field_simp
  rw [he]
  exact Real.cos_arccos x.property.1 x.property.2

end Erdos1133
