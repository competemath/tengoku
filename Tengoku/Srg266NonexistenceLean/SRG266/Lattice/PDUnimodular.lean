/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.LinearAlgebra.BilinearForm.Properties
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank
import Tengoku.Seed.LinearAlgebra.FreeModule.Basic
import Tengoku.Seed.RingTheory.Finiteness.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

structure PDUnimodularLattice (n : ℕ) where

  carrier : ModuleCat ℤ
  [moduleFree : Module.Free ℤ carrier]
  [moduleFinite : Module.Finite ℤ carrier]

  pairing : LinearMap.BilinForm ℤ carrier

  symmetric : pairing.IsSymm

  positiveDefinite : ∀ v : carrier, v ≠ 0 → 0 < pairing v v

  unimodular : Function.Bijective pairing

  rank : Module.finrank ℤ carrier = n

end SRG266
