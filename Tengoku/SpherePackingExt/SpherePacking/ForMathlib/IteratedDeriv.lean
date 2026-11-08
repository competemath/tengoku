module
public import Tengoku.Seed.Analysis.Calculus.ContDiff.Bounds
public import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
public import Tengoku.Seed.Analysis.Complex.Exponential
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
public import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
public import Tengoku.Seed.Analysis.Complex.RealDeriv
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.DerivHelpers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Iterated derivative helpers

This file collects small lemmas about `iteratedDeriv` and `iteratedFDeriv` that are duplicated
across the project.
-/

namespace SpherePacking.ForMathlib

open scoped Topology
open Filter

end SpherePacking.ForMathlib
