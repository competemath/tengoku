import Tengoku.MagicSquaresFieldsLean.MagicSquares.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-- `x` is an `n`-th power; this convention automatically includes zero.-/
def IsNthPower {R : Type*} [Monoid R] (n : ℕ) (x : R) : Prop :=
  ∃ y : R, y ^ n = x

/-- A magic square whose entries are distinct `n`-th powers.-/
def IsMagicOfPowers {R : Type*} [CommRing R] (n : ℕ) (M : Square3 R) : Prop :=
  M.IsMagic ∧ M.PairwiseDistinct ∧ ∀ k : Fin 9, IsNthPower n (M.entries k)

/-- `R` is `n`-Parker: no 3 × 3 magic square of nine distinct `n`-th powers exists.-/
def IsNParker (R : Type*) [CommRing R] (n : ℕ) : Prop :=
  ¬ ∃ M : Square3 R, IsMagicOfPowers n M

/-- The original Parker condition is the case `n = 2`.-/
def IsParker (R : Type*) [CommRing R] : Prop :=
  IsNParker R 2

end MagicSquares
