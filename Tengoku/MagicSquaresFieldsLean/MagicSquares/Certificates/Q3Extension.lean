import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field343
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field1331
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field2187
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field6859
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field12167
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field16807
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field19683
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field29791
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field79507
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field103823
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field161051
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field177147
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field205379
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field300763
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field357911
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.Q3Extension.Field493039

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates

/-- All sixteen positive extension-field cases below 553736.-/
theorem not_squareParker_of_card_q3_extension {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F ∈ ([343, 1331, 2187, 6859, 12167, 16807, 19683, 29791, 79507, 103823, 161051, 177147, 205379, 300763, 357911, 493039] : List ℕ)) : ¬ IsParker F := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcard
  rcases hcard with hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard | hcard
  · exact not_squareParker_of_card_343 hcard
  · exact not_squareParker_of_card_1331 hcard
  · exact not_squareParker_of_card_2187 hcard
  · exact not_squareParker_of_card_6859 hcard
  · exact not_squareParker_of_card_12167 hcard
  · exact not_squareParker_of_card_16807 hcard
  · exact not_squareParker_of_card_19683 hcard
  · exact not_squareParker_of_card_29791 hcard
  · exact not_squareParker_of_card_79507 hcard
  · exact not_squareParker_of_card_103823 hcard
  · exact not_squareParker_of_card_161051 hcard
  · exact not_squareParker_of_card_177147 hcard
  · exact not_squareParker_of_card_205379 hcard
  · exact not_squareParker_of_card_300763 hcard
  · exact not_squareParker_of_card_357911 hcard
  · exact not_squareParker_of_card_493039 hcard

end MagicSquares.Certificates
