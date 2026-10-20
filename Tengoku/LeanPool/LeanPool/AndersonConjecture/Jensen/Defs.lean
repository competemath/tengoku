/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku.Seed.RingTheory.AdicCompletion.Algebra
public import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Defs
import Tengoku.Seed.Tactic.ContinuousFunctionalCalculus

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trivial Generic Formal Fiber

A Noetherian local domain A has trivial generic formal fiber if
every prime of its adic completion contracting to zero is itself
zero. This is the key condition in Jensen's construction of UFDs
with prescribed completions.
-/

@[expose] public section

/-- A local ring `R` has **trivial generic formal fiber** if every
prime ideal of its `M`-adic completion that contracts to `0` in `R` is
itself `0`. (This is the relevant condition for Noetherian local domains.) -/
def HasTrivialGenericFormalFiber
    (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (P : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)),
    P.IsPrime →
    Ideal.comap
      (algebraMap R
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)) P = ⊥ →
    P = ⊥
