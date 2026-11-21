/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Tengoku.LeanSpectralTheory.Spectral.Spectral.Existence
import Tengoku.LeanSpectralTheory.Spectral.PVM.Unbounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable spectral functional calculus

This file defines the spectral functional calculus `spectralFuncCalc A hA f hf`
by applying a self-adjoint operator's representing PVM's unbounded integral to
a measurable function `f`, and shows it recovers `A` on the coordinate
function.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
