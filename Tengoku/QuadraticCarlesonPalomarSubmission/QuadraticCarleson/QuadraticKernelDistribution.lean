/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.Definitions
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PrincipalValueDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The quadratically modulated principal-value kernel

The kernel in the paper is the product of the smooth phase
`y ↦ e(λ y²)` and the tempered distribution `p.v. (1 / y)`.
-/

open scoped SchwartzMap

namespace QuadraticCarleson

/--
@isnad1 id=hastempe.0h1v.s5.1ea6a7047525 from=translated src=- shape=445ff312 vocab=84c0d503
-/
theorem quadraticPhase_hasTemperateGrowth (modulation : ℝ) :
    (fun y : ℝ => phase (modulation * y ^ 2)).HasTemperateGrowth := by
  rw [show (fun y : ℝ => phase (modulation * y ^ 2)) =
      (fun u : ℝ => Complex.exp (u * Complex.I)) ∘
        fun y : ℝ => 2 * Real.pi * (modulation * y ^ 2) by
    funext y
    simp only [Function.comp_apply, phase]]
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- The distribution `e(λ y²) · p.v. (1 / y)`.-/
noncomputable def quadraticKernelDistribution (modulation : ℝ) : 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ
    (fun y : ℝ => phase (modulation * y ^ 2)) principalValueOneDiv

/--
@isnad1 id=eq.0h2v.s10.1d64081eb15f from=translated src=- shape=42cdf611 vocab=0026d5e2
-/
theorem quadraticKernelDistribution_apply (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) :
    quadraticKernelDistribution modulation f =
      principalValueOneDiv
        (SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => phase (modulation * y ^ 2)) f) := by
  rfl

end QuadraticCarleson
