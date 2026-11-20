/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEGram
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

set_option maxRecDepth 4096 in
theorem gramA_four_det : (gramA 4).det = 5 := by decide

set_option maxRecDepth 16384 in
theorem gramE_six_det : (gramE 6).det = 3 := by decide

end SRG266.Lattice
