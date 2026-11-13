import Tengoku.Seed.Analysis.Normed.Algebra.Basic
import Tengoku.Seed.Topology.MetricSpace.Contracting
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A bounded Riccati fixed point

This module proves the contraction argument used in the identity-corner construction.
The algebra is allowed to be noncommutative. The analytic assumptions are those of
a complete normed real algebra. No expander theorem is assumed in this module.
-/

namespace NoEpsilon

open scoped NNReal

section NormBounds

variable {E : Type*} [NormedRing E]

/-- The quadratic expression appearing in the fixed-point equation.-/
def quadratic (c d e x : E) : E := x * x + c * x + x * d + e

/-- Difference estimate retaining the order of noncommuting factors.-/
theorem norm_quadratic_sub_le (c d e x y : E) :
    ‖quadratic c d e x - quadratic c d e y‖ ≤
      (‖x‖ + ‖y‖ + ‖c‖ + ‖d‖) * ‖x - y‖ := by
  have hid : quadratic c d e x - quadratic c d e y =
      (x - y) * x + y * (x - y) + c * (x - y) + (x - y) * d := by
    dsimp [quadratic]
    noncomm_ring
  rw [hid]
  calc
    ‖(x - y) * x + y * (x - y) + c * (x - y) + (x - y) * d‖
        ≤ ‖(x - y) * x‖ + ‖y * (x - y)‖ + ‖c * (x - y)‖ +
            ‖(x - y) * d‖ := by
          linarith [norm_add_le ((x - y) * x) (y * (x - y)),
            norm_add_le ((x - y) * x + y * (x - y)) (c * (x - y)),
            norm_add_le ((x - y) * x + y * (x - y) + c * (x - y)) ((x - y) * d)]
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ + ‖c‖ * ‖x - y‖ +
          ‖x - y‖ * ‖d‖ := by
          gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

end NormBounds

section FixedPoint

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- The Riccati map with a scalar parameter and specified centre.-/
noncomputable def riccatiMap (b c d e : E) (ε : ℝ) (x : E) : E :=
  b + ε • quadratic c d e x

/-- An explicit positive scale determined by the coefficient norms.-/
noncomputable def riccatiScale (b c d e : E) : ℝ :=
  2 * (((‖b‖ + 1) ^ 2 + (‖c‖ + ‖d‖) * (‖b‖ + 1) + ‖e‖) +
    (2 * (‖b‖ + 1) + ‖c‖ + ‖d‖) + 1)

end FixedPoint

end NoEpsilon
