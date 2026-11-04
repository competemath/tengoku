/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.Depth
import Tengoku.Seed.RingTheory.KrullDimension.Regular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohen--Macaulay local rings

This file compares the homological local depth from `RiemannRoch.Chow.Depth` with Krull
dimension and begins the quotient-by-a-regular-element stability theory.
-/

noncomputable section

universe u

open CategoryTheory Abelian RingTheory.Sequence

variable (R : Type u) [CommRing R] [IsLocalRing R]

namespace ModuleCat

/-- The depth of a local ring as a module over itself.-/
def ringDepth : ℕ∞ :=
  localDepth (ModuleCat.of R R)

/-- Krull dimension of a nontrivial ring, with the impossible bottom value removed.-/
def localKrullDim : ℕ∞ :=
  (ringKrullDim R).unbot <| by
    exact (lt_of_lt_of_le (WithBot.bot_lt_coe 0) ringKrullDim_nonneg_of_nontrivial).ne'

/--
@isnad1 id=eq.0h1v.s4.241b126dee14 from=translated src=- shape=8309a0b6 vocab=6cb8dbb0
-/
@[simp]
theorem coe_localKrullDim :
    (localKrullDim R : WithBot ℕ∞) = ringKrullDim R :=
  WithBot.coe_unbot _ _

/-- A Noetherian local ring is Cohen--Macaulay when its homological depth equals its
Krull dimension.-/
class IsCohenMacaulayLocalRing : Prop where
  depth_eq_dimension : ringDepth R = localKrullDim R

/-- A quotient of a local ring by a principal ideal contained in the maximal ideal is local.
The explicit construction avoids a global quotient-local-ring instance, which would be invalid
for the trivial quotient.-/
def quotientSpanIsLocalRing (r : R) (hrm : r ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {r}) := by
  letI : Nontrivial (R ⧸ Ideal.span {r}) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    exact (lt_of_le_of_lt (Ideal.span_le.mpr (by simpa using hrm))
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top).ne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {r}))
    Ideal.Quotient.mk_surjective

end ModuleCat
