/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.BlockLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # ProductAnnulusLocalization -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# ProductAnnulusLocalization

Finite block-localization scaffold for product annuli and coefficient windows.
-/

private def coeffBlockFinset_wip {d : Nat} (ℓ : Idx d) : Finset (Idx d) :=
  Fintype.piFinset fun q : Fin d => HermiteLEAN.squareBlock (ℓ q)

private def nearBlocks_wip {d : Nat} (j : Idx d) (M : Nat) : Finset (Idx d) :=
  (Fintype.piFinset fun q : Fin d => Finset.range (j q + M + 1)).filter fun ℓ =>
    Hermite1DimdLEAN.blockDistance j ℓ ≤ M

private def nearLowBlocks_wip {d : Nat} (J M : Nat) : Finset (Idx d) :=
  (lowAnnuli d J).biUnion fun j => nearBlocks_wip j M

private def nearLowCoeffSet_wip {d : Nat} (J M : Nat) : Finset (Idx d) :=
  (nearLowBlocks_wip (d := d) J M).biUnion fun ℓ => coeffBlockFinset_wip ℓ

end DimdPolyLEAN
