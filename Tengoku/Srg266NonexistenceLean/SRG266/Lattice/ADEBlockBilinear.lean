/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockCoordinates
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

def adeRootRatForm (ts : List ADEType) :
    LinearMap.BilinForm ℚ (Fin (ADEType.rankSum ts) → ℚ) :=
  Matrix.toBilin' (fun i j => ((adeGram ts).2 i j : ℚ))

def adeBlockRatForm (ts : List ADEType) :
    LinearMap.BilinForm ℚ (ADEBlockIndex ts → ℚ) :=
  Matrix.toBilin' (fun i j => (adeBlockPairing ts i j : ℚ))

/--
@isnad1 id=eq.0h2v.s9.f47271aafa21 from=translated src=- shape=be8fbce0 vocab=4a94d243
-/
@[simp]
theorem adeBlockRatForm_nil (x y : ADEBlockIndex [] → ℚ) :
    adeBlockRatForm [] x y = 0 := by
  simp only [adeBlockRatForm, Matrix.toBilin'_apply]
  change (∑ i : Empty, ∑ j : Empty, x i * (adeBlockPairing [] i j : ℚ) * y j) = 0
  simp

end SRG266.Lattice
