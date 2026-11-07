/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Algebra.Star.StarProjection
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.LinearAlgebra.UnitaryGroup
import Tengoku.Seed.Topology.Instances.Matrix
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A continuous unitary path to the factor swap

arXiv:1703.09188 requires a continuous unitary interpolation from the identity
matrix to the factor swap in Proposition `prop:U2-U3-trivial-tr-transpose`,
lines 2143--2155, and Proposition `prop:U1-U2-equiv-ancillatrick`, lines
2226--2235.

The factor swap acts by `Matrix.swapMatrix d`. We give a concrete interpolation
by decomposing the tensor-square space into its symmetric and antisymmetric
subspaces and rotating only the antisymmetric subspace by the phase
`exp (π x I)`.
-/

open scoped ComplexConjugate Matrix

namespace Matrix

variable (d : ℕ)

/-- The unit complex phase used on the antisymmetric subspace.-/
noncomputable def swapPhase (x : ℝ) : ℂ :=
  Complex.exp ((Real.pi * x : ℝ) * Complex.I)

/-- The swap phase times its complex conjugate is one.
@isnad1 id=eq.0h1v.s5.eec869728269 from=translated src=- shape=ef137c3b vocab=4a38d46e
-/
theorem swapPhase_mul_star (x : ℝ) :
    swapPhase x * star (swapPhase x) = 1 := by
  change Complex.exp ((Real.pi * x : ℝ) * Complex.I) *
    conj (Complex.exp ((Real.pi * x : ℝ) * Complex.I)) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

end Matrix
