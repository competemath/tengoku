/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEComponentScalar
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SeparatedCoordinateProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

def a11D7E6Types : List ADEType := [.A 11, .D 7, .E6]

def a11D7E6D7BlockScalar : ADEBlockIndex a11D7E6Types → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr i)) => nomatch i

def a11D7E6D7Scalar (i : Fin 24) : ℚ :=
  a11D7E6D7BlockScalar (finADEBlockEquiv a11D7E6Types i)

def a11D7E6D7Projection : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) where
  toFun u i := a11D7E6D7Scalar i * u i
  map_add' u v := by ext i; simp [mul_add]
  map_smul' r u := by ext i; simp [mul_left_comm]

/--
@isnad1 id=eq.0h1v.s8.41257f9652f8 from=translated src=- shape=bffbcb2a vocab=8b407795
-/
theorem a11D7E6D7Projection_single (i : Fin 24) :
    a11D7E6D7Projection (Pi.single i 1) = a11D7E6D7Scalar i • Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst j; simp [a11D7E6D7Projection]
  · simp [a11D7E6D7Projection, h]

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

end SRG266.Lattice
