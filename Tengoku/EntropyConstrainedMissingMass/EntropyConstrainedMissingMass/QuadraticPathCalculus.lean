import Tengoku.Seed.Analysis.Calculus.Deriv.Pow
import Tengoku.Seed.Analysis.Calculus.Deriv.Add
import Tengoku.Seed.Analysis.Calculus.Deriv.Comp
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact first and second jets of finite sums along quadratic coordinate paths. -/
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter
open scoped Topology

/-- Quadratic coordinate path with prescribed first and second coefficients.-/
def quadraticPath (a b c r : ℝ) : ℝ := a + b * r + c * r ^ 2

@[simp] theorem quadraticPath_zero (a b c : ℝ) : quadraticPath a b c 0 = a := by
  simp [quadraticPath]

end
end EntropyConstrainedMissingMass
