module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Biplane23632
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Forcing the canonical `2-(6,3,2)` design

This is the deterministic reconstruction step in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`, Lemma `23632_unique`.

Assuming `012, 014, 023, 125` are blocks of a `2-(6,3,2)` design, the remaining six blocks are
forced by pair multiplicities.

## Main statement
* `Design23632.forced_of_initial_blocks`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section
namespace Design23632

/-- The set of blocks in `T` containing the given pair of points.-/
public def blocksThroughPair (T : Finset Block) (x y : Point) : Finset Block :=
  T.filter (fun B => x ∈ B ∧ y ∈ B)

/-- Membership characterization for `blocksThroughPair`.-/
@[simp] public lemma mem_blocksThroughPair {T : Finset Block} {x y : Point} {B : Block} :
    B ∈ blocksThroughPair T x y ↔ B ∈ T ∧ x ∈ B ∧ y ∈ B := by
  simp [blocksThroughPair, and_assoc, and_comm]

attribute [grind =_] mem_blocksThroughPair

/-- The cardinality of `blocksThroughPair` is `pairCount`.-/
public lemma blocksThroughPair_card (T : Finset Block) (x y : Point) :
    (blocksThroughPair T x y).card = pairCount T x y := by
  rfl

attribute [grind =_] blocksThroughPair_card

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
