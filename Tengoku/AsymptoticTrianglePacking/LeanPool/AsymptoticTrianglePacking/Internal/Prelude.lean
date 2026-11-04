/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import Tengoku.Seed.Analysis.Complex.ExponentialBounds
public import Tengoku.Seed.Data.Finset.Functor
public import Tengoku.Seed.Data.List.GetD
public import Tengoku.Seed.Analysis.Real.Sqrt
public import Tengoku.Seed.MeasureTheory.Integral.Average
public import Tengoku.Seed.Probability.Moments.SubGaussian
public import Tengoku.Seed.Probability.ProbabilityMassFunction.Integrals
public import Tengoku.Seed.Tactic.NormNum.BigOperators
public import Tengoku.Seed.Tactic.NormNum.Prime
public import Tengoku.Seed.Tactic.NormNum.RealSqrt
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shared Mathlib prelude for the extracted asymptotic triangle-packing modules

Common imports for the modules in this package. Individual modules may import additional
Mathlib files for their own proofs.
-/
