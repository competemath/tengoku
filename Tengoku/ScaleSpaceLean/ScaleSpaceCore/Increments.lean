/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.LevyExtraction
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Exponent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `thm:increments-levy`: every increment exponent is a symmetric Lévy exponent

Home: line:thm:increments-levy

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`.

`LevyExtraction` produced a finite measure `ϱ` on `[0,∞)` with

  `∫ k_ω dϱ = g_{s,t}(ω)` for every `ω`,  `k_ω(x) = (1 - cos ωx)/(1 ∧ x²)`, `k_ω(0) = ω²/2`.

What is left is the last paragraph of the blueprint's proof: read `ϱ` in two pieces, the atom at
the origin and the rest. The atom is the Gaussian coefficient — that is what filling the
removable singularity of `k_ω` bought — and the rest, divided back by the weight, is the Lévy
measure:

  `a := ϱ(\{0\})/2`,  `ν := (1 ∧ x²)^{-1}\,ϱ|_{(0,∞)}`,

for which `∫ (1 ∧ x²)\,dν = ϱ((0,∞)) < ∞` and `a ω² + ∫ (1 - \cos ωx)\,dν(x) = ∫ k_ω\,dϱ`. There
is no atom at infinity to exclude, because tightness has already forbidden it, and
correspondingly no killing term — the point at which the spatial argument differs from the
causal one, where the killing term is admitted by the compactification and excluded afterwards.

## Infinite divisibility

The last sentence of the node is stated at the transform, because Mathlib has no convolution
power of measures. It is the only place in Chapter 5 where the trust boundary is spent: the
`n`-th root of `\hat\mu_{s,t}` is the transform of a probability measure because the pair
`(a/n, ν/n)` is again a symmetric Lévy pair, and that is `prop:fourier-toolbox`(3)'s converse
together with (1) — ledger **A1** and **A3**.

twin: `Hemigroup.CascadeCore.exponent_hasLevyRep` (`Hemigroup/LevyTriple.lean`).

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Increments.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology NNReal

/-! ## The split of the limit measure at the origin -/

/-- The Lévy measure read off the limit measure: the weight `1 ∧ x²` divided back out, on
`(0,∞)`.-/
noncomputable def limitLevyMeasure (ϱ : Measure ℝ) : Measure ℝ :=
  (ϱ.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (min 1 (x ^ 2))⁻¹

/-! ## The theorem -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ}

end ScaleSpace
