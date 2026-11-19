import Tengoku.MagicSquaresFieldsLean.MagicSquares.CubePrimeClassification
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.CubicModels
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.QuadraticPositive
import Tengoku.MagicSquaresFieldsLean.MagicSquares.PowerIndexOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete classification of 3-Parker fields (paper, Theorem 13.1)

The center-zero existence bound reduces the problem to odd prime powers
below 1037. Prime fields use `cubeParker_iff_of_prime_card`. Extension fields
fall into three groups: trivial cube index, explicit positive witnesses,
and the two exceptions of cardinalities 25 and 343.

The finite coverage lemma proves that this case split is exhaustive.
The final reverse implication transports the negative certificates.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares
open Certificates

local instance cubeClassificationDecidablePrime (n : ℕ) : Decidable n.Prime := Nat.decidablePrime' n

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Exhaustive arithmetic coverage; each listed order is handled below.

omit [DecidableEq F] in
/-- Positive certificates for all extension fields with nontrivial cube index
below the analytic bound, apart from the two certified exceptions.-/
theorem not_cubeParker_of_card_extension_witness
    (hq : Fintype.card F ∈ ([49, 121, 169, 289, 361, 529, 625, 841, 961] : List ℕ)) : ¬ IsNParker F 3 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq
  · intro h
    have hc : Fintype.card F = Fintype.card Field49 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_49⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field121 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_121⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field169 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_169⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field289 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_289⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field361 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_361⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field529 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_529⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field625 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_625⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field841 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_841⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field961 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_961⟩

end MagicSquares
