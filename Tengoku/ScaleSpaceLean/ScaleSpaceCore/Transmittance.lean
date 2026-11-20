/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Additivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `cor:smoothed-transmittance`: one strictly monotone number per scale

Home: line:cor:smoothed-transmittance

Blueprint: `blueprint/src/parts/05-cascade.tex`, `cor:smoothed-transmittance`.

The coordinate the gauge argument of Chapter 6 runs on, and the one node of Chapter 5 with no
causal counterpart: the causal argument read the action off the accumulated exponent at one
fixed value of the transform variable, which `cor:monotonicity` does not licence on the line.
What replaces it is

  `Θ(t) = ∫ μ̂_{0,t}(ω) ρ(ω) dω = ∫ e^{-x²/2} μ_{0,t}(dx)`,

a single number attached to each scale, continuous, in `(0,1]`, and — under (ND) — strictly
decreasing.

The Gaussian density `ρ` of the statement is `ScaleSpace.gaussTest`, the same test function
`Pairing` uses for the uniqueness clause, and the Fubini identity of the first
clause is `integral_cos_mul_gaussTest` read in the other variable: the cosine moment of the
standard Gaussian density is `e^{-x²/2}` at frequency `x`, which is exactly the integrand on the
measure side.

## What proving it found

Two of the six clauses need less than the blueprint's proof cites. Positivity of `Θ` is *not*
`lem:nonvanishing`: the integrand `e^{-x²/2}` is strictly positive at every point, so the
integral of a probability measure against it is positive for the elementary reason, and the
formal proof spends no positivity of the transform. Only the antitone clause and the strict
clause use `kernel_transform_pos`, and the strict one uses it only to know that the factor
`μ̂_{0,s} ρ` is positive.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Transmittance.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The Gaussian density, written as the statement writes it -/

lemma gaussTest_apply (ω : ℝ) :
    gaussTest ω = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(ω ^ 2) / 2) := by
  simp [gaussTest, gaussianPDFReal]

lemma gaussTest_pos (x : ℝ) : 0 < gaussTest x := gaussianPDFReal_pos 0 1 x one_ne_zero

lemma continuous_gaussTest : Continuous gaussTest := by
  have h : gaussTest = fun ω => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(ω ^ 2) / 2) :=
    funext gaussTest_apply
  rw [h]
  fun_prop

/-! ## The Fubini identity -/

/-! ## The clauses -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

end ScaleSpace
