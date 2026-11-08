module
public import Tengoku.Seed.Data.Finset.Card
public import Tengoku.Seed.Data.Finset.Powerset
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Data.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic facts about the `2-(11,5,2)` biplane

We use a convenient axiomatisation matching the construction in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`:
we start from a family of `11` subsets of an `11`-set, each of size `5`, with constant pairwise
intersection size `2`. From this we derive the usual biplane parameters:
each point lies in exactly `5` blocks, and each pair of points lies in exactly `2` blocks.

## Main definitions
* `Biplane.Structure`
* `Biplane.Structure.r`
* `Biplane.Structure.lam`

## Main statements
* `Biplane.Structure.sum_r_eq_55`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace Biplane

/-- The point type for the `2-(11,5,2)` biplane.-/
public abbrev Point := Fin 11
/-- A block is a finite set of points. In a `Biplane.Structure`, blocks have cardinality `5`.-/
public abbrev Block := Finset Point

/-- An axiomatisation of a `2-(11,5,2)` biplane by constant block intersections.-/
public structure Structure where
  blocks : Finset Block
  blocks_card : blocks.card = 11
  block_card : ∀ B ∈ blocks, B.card = 5
  inter_card : ∀ ⦃B B'⦄, B ∈ blocks → B' ∈ blocks → B ≠ B' → (B ∩ B').card = 2

namespace Structure

variable (D : Structure)

/-- For a point `x`, the number of blocks of the biplane containing `x`.-/
@[expose] public def r (x : Point) : ℕ :=
  (D.blocks.filter fun B => x ∈ B).card

/-- For points `x,y`, the number of blocks of the biplane containing both `x` and `y`.-/
@[expose] public def lam (x y : Point) : ℕ :=
  (D.blocks.filter fun B => x ∈ B ∧ y ∈ B).card

private def incidences (B : Block) : Finset (Point × Block) :=
  B.product {B}

private lemma mem_incidences {B : Block} {p : Point × Block} :
    p ∈ incidences B ↔ p.1 ∈ B ∧ p.2 = B := by
  rcases p with ⟨x, B0⟩
  simp [incidences, eq_comm]

attribute [grind =] mem_incidences

end Biplane.Structure
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
