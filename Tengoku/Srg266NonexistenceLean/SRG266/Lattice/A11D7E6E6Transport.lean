/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockBilinear
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6Projection
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.E6CartanShortNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

def a11D7E6E6Part {K : Type*} (u : Fin 24 → K) (i : Fin 6) : K :=
  u ((finADEBlockEquiv a11D7E6Types).symm (Sum.inr (Sum.inr (Sum.inl i))))

def a11D7E6E6Lift {K : Type*} [Zero K] (u : Fin 6 → K) (i : Fin 24) : K :=
  match finADEBlockEquiv a11D7E6Types i with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl j)) => u j
  | Sum.inr (Sum.inr (Sum.inr j)) => nomatch j

theorem a11D7E6E6Lift_intCast (z : Fin 6 → ℤ) :
    a11D7E6E6Lift (intCoordsToRat z) = intCoordsToRat (a11D7E6E6Lift z) := by
  ext i
  simp only [intCoordsToRat_apply]
  unfold a11D7E6E6Lift
  rcases finADEBlockEquiv a11D7E6Types i with j | (j | (j | j))
  · rfl
  · rfl
  · rfl
  · exact j.elim

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

end SRG266.Lattice
