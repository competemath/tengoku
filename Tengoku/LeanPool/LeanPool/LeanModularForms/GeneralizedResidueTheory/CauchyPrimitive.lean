/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku

/-!
# Holomorphic Primitives on Convex Sets

Construction of a primitive F for a holomorphic function f on a convex
open set S via the segment integral F(z) = ∫₀¹ f(c + t(z-c))·(z-c) dt.

## Main Results

* `holomorphic_convex_primitive` — holomorphic on convex open ⇒ has primitive
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

-- Needed in mathlib v4.29 where these instances are no longer synthesized automatically
attribute [local instance] IsScalarTower.complexToReal

private instance instNormSMulClassRealComplex : NormSMulClass ℝ ℂ :=
  NormedSpace.toNormSMulClass

private instance instIsBoundedSMulRealComplex : IsBoundedSMul ℝ ℂ :=
  NormSMulClass.toIsBoundedSMul

private instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ :=
  IsBoundedSMul.continuousSMul

end
