import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SeparableRelation
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff
import Tengoku.Seed.Analysis.Calculus.ContDiff.Polynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Smoothness of continuous algebraic root selections outside a finite
exceptional set. Simple-root relations come from `SeparableRelation`;
the ordinary real implicit-function theorem then identifies the given
continuous selection with a smooth local branch. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Polynomial Filter
open scoped Topology

def bivariateEval (P : Polynomial (Polynomial ℝ)) (q : ℝ × ℝ) : ℝ :=
  (P.map (Polynomial.evalRingHom q.1)).eval q.2

theorem realLinearMap_isInvertible {L : ℝ →L[ℝ] ℝ} (hL : L 1 ≠ 0) : L.IsInvertible := by
  have he (a : ℝ) : L a = a * L 1 := by simpa using L.map_smul a (1 : ℝ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext
    intro a
    change L ((L 1)⁻¹ * a) = a
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro a
    change (L 1)⁻¹ * L a = a
    rw [he a]
    field_simp

end
end DuistermaatVanDerKallen
