/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PVSymmetricLimit
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.QuadraticKernelDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Symmetric truncations of the quadratic kernel

The distribution `e(λx²) · p.v. (1/x)` is the limit of its ordinary
symmetric truncations on every Schwartz test function.
-/

open Filter
open scoped SchwartzMap Topology

namespace QuadraticCarleson

/-- The ordinary symmetric truncation of the quadratic kernel paired with a
Schwartz test function.-/
noncomputable def quadraticKernelTruncationAction
    (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) : ℂ :=
  principalValueTruncation ε
    (SchwartzMap.smulLeftCLM ℂ
      (fun y : ℝ ↦ phase (modulation * y ^ 2)) f)

/--
@isnad1 id=eq.0h3v.s7.60ec06786cb7 from=translated src=- shape=fe4c1f98 vocab=3f1c99e3
-/
theorem quadraticKernelTruncationAction_eq_integral
    (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) :
    quadraticKernelTruncationAction modulation ε f =
      ∫ y in {y : ℝ | ε < |y|},
        phase (modulation * y ^ 2) * f y / (y : ℂ) := by
  simp [quadraticKernelTruncationAction, principalValueTruncation,
    SchwartzMap.smulLeftCLM_apply_apply
      (quadraticPhase_hasTemperateGrowth modulation), smul_eq_mul]

/-- The distributional quadratic kernel agrees with the limit of ordinary
symmetric truncations as the deleted radius tends to zero from above.
@isnad1 id=tendsto.0h2v.s8.472bc8d19391 from=translated src=- shape=3f79d002 vocab=5c1b1996
-/
theorem tendsto_quadraticKernelTruncationAction
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ ↦ quadraticKernelTruncationAction modulation ε f)
      (𝓝[>] 0) (𝓝 (quadraticKernelDistribution modulation f)) := by
  simpa only [quadraticKernelTruncationAction, quadraticKernelDistribution_apply,
    principalValueOneDiv_apply] using
      tendsto_principalValueTruncation
        (SchwartzMap.smulLeftCLM ℂ
          (fun y : ℝ ↦ phase (modulation * y ^ 2)) f)

end QuadraticCarleson
