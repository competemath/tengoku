/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # FunctionsBoundedAtInfty -/

@[expose] public section

open UpperHalfPlane

/-This is from the Sphere Pack project, so might not actually be for mathlib.-/

theorem isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, Pi.neg_apply, norm_neg]

alias ⟨_, IsBoundedAtImInfty.neg⟩ := isBoundedAtImInfty_neg_iff
