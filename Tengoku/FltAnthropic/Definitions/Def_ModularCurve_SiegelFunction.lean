import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def siegelFun (N : ℕ) (r s : ℤ) (z : ℂ) : ℂ :=
  -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
    (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
    ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
      (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹))

/--
@isnad1 id=eq.0h4v.s9.e031f72f30fc from=translated src=- shape=787e5114 vocab=d8c54928
-/
theorem siegelFun_def (N : ℕ) (r s : ℤ) (z : ℂ) :
    siegelFun N r s z =
      -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
        ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
          (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹)) :=
  rfl

end ModularCurve

end
