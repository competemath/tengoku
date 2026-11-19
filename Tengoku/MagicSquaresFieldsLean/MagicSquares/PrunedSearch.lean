import Tengoku.MagicSquaresFieldsLean.MagicSquares.NormalizedSearch

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The arithmetic power test, including zero.-/
def powerEntryTest (n : ℕ) (x : F) : Prop :=
  x = 0 ∨ x ^ ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1

instance (n : ℕ) (x : F) : Decidable (powerEntryTest n x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x ^
    ((Fintype.card F - 1) / powerIndex n (Fintype.card F)) = 1))

/-- Both entries opposite the center must be powers. Filtering these offsets
before the two-parameter search substantially reduces finite certificates.-/
def centerOnePowerOffsets (n : ℕ) : Finset F :=
  Finset.univ.filter fun u => powerEntryTest n (1 + u) ∧ powerEntryTest n (1 - u)

/-- An equivalent search that restricts both center-one parameters to offsets
whose opposite entries pass the power test.-/
def prunedPowerSearchSucceeds (n : ℕ) : Bool :=
  decide ((∃ x : F, normalizedPowerConditions n (Square3.centerZero x)) ∨
    (∃ u ∈ centerOnePowerOffsets (F := F) n,
      ∃ v ∈ centerOnePowerOffsets (F := F) n,
        normalizedPowerConditions n (Square3.centerOne u v)))

end MagicSquares
