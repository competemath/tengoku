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
/--
@isnad1 id=eq.0h0v.s5.2507441a3bd7 from=translated src=- shape=ec3b48e7 vocab=127c15cf
-/
theorem gramA_four_det : (gramA 4).det = 5 := by decide

set_option maxRecDepth 16384 in
/--
@isnad1 id=eq.0h0v.s5.1aa2515fc0c4 from=translated src=- shape=ec3b48e7 vocab=8f8b47f9
-/
theorem gramE_six_det : (gramE 6).det = 3 := by decide

end SRG266.Lattice
