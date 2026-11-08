module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDerived

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deriving `S(3,6,22)` from `S(5,8,24)`

This is the standard "derived design" construction: given a Steiner system `S(5,8,24)` and fixed
points `0,1`, consider the blocks containing both points and delete these two points, obtaining a
family of `6`-subsets of `Fin 22`. This family forms a Steiner system `S(3,6,22)`.

## Main definitions
* `DerivedS3622.derivedBlocks`
* `DerivedS3622.derivedSteinerSystem`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace DerivedS3622

/-- The blocks of the derived `S(3,6,22)` design, obtained from blocks of `S` containing `0,1`.-/
@[expose] public def derivedBlocks (S : SteinerSystem 24 8 5) : Set (Finset (Fin 22)) :=
  {B22 | ∃ B24 : Finset (Fin 24),
      B24 ∈ S.blocks ∧ (0 : Fin 24) ∈ B24 ∧ (1 : Fin 24) ∈ B24 ∧ B22 = drop2 B24}

end DerivedS3622

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
