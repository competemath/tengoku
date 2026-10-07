/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Internal

/-!
# Pathwidth from a cubic bisection bound

This completes the reduction in Fomin and Høie's *Pathwidth of cubic graphs
and exact algorithms* (2006), Theorem 5. For any cut of a subcubic graph,
the decompositions of its sides and their boundary graph concatenate with
the explicit finite bound below. For balanced cuts, every positive linear
slack absorbs the logarithmic remainder.

`Bisection.Helpful` proves the Monien–Preis theorem asserting
`BisectionBound ξ N₀` for every positive `ξ` and some `N₀`, then applies
this reduction to obtain the sharp pathwidth bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- Every cubic graph admits a balanced cut of size at most `3n/2`, simply
because this counts all its edges. This coarse instance is unconditional. -/
theorem bisectionBound_coarse : BisectionBound (4 / 3) 0 :=
  PathDecomposition.Internal.bisectionBound_coarse

/-- Increasing the slack and the size threshold weakens the bisection bound. -/
theorem BisectionBound.mono {ξ ξ' : ℝ} {N₀ N₁ : Nat} (h : BisectionBound ξ N₀)
    (hξ : ξ ≤ ξ') (hN : N₀ ≤ N₁) : BisectionBound ξ' N₁ := by
  intro W _ _ H _ regular large
  obtain ⟨S, hleft, hright, hcut⟩ := h W H regular (hN.trans_lt large)
  refine ⟨S, hleft, hright, hcut.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end Algebraic.Cutwidth
