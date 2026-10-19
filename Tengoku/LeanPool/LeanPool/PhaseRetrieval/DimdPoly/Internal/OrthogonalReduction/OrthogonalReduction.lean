/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.Seed.Analysis.InnerProductSpace.Basic
public import Tengoku.Seed.MeasureTheory.Function.LpSpace.Basic
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.ImportedAnalyticInputs
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.LpNorm
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # OrthogonalReduction -/

@[expose] public section

noncomputable section

open scoped BigOperators ENNReal
open Complex MeasureTheory Real

namespace OrthogonalReduction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)
variable [MeasureTheory.SigmaFinite μ]

private def localDefect (ι : H →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ) (f0 : H) (h : H) : ℝ :=
  MeasureTheory.lpNorm
    (fun x : Ω => ‖(ι (h + f0) : Ω → ℂ) x‖ - ‖(ι f0 : Ω → ℂ) x‖)
    2 μ

/-
Scaffolding theorem: local stability in `L²(μ)`.

This is the abstract orthogonal-reduction step from `HermiteSPR.tex`,
Theorem 2.4. The defect is the `L²` norm of the pointwise modulus difference,
encoded in mathlib via `eLpNorm` of a real-valued function.
-/

end OrthogonalReduction
