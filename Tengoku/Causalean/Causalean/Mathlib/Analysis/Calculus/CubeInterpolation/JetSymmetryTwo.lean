module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Tengoku

/-!
# Second derivatives of finite jets

Finite `C^(n+2)` regularity makes the order-`n` derivative a `C²` map.
The library's second-derivative symmetry then applies to that lower jet.
An evaluation bridge identifies its second derivative with the first two
slots of the order-`n+2` derivative of the original map.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The order-`n` iterated derivative of a `C^(n+2)` real function is `C²`
at the same point. -/
theorem finite_order_lower_jet_contDiffAt_two {d n : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ (n + 2) u x) :
    ContDiffAt ℝ 2 (iteratedFDeriv ℝ n u) x := by
  exact hu.iteratedFDeriv_right (m := 2) (i := n)
    (by exact le_of_eq (add_comm (2 : WithTop ℕ∞) (n : WithTop ℕ∞)))

/-- At a `C^(n+2)` point, the second derivative of the order-`n` jet is
symmetric in its two input directions. -/
theorem finite_order_lower_jet_second_symmetric {d n : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ (n + 2) u x) (a b : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n u)) x a b =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n u)) x b a := by
  exact (finite_order_lower_jet_contDiffAt_two hu).isSymmSndFDerivAt
    (by norm_num) a b

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
