/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanAZeroSum
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ZeroSumDualCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def cartanARatForm (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → ℚ) :=
  Matrix.toBilin' (fun i j => (gramA n i j : ℚ))

end SRG266.Lattice
