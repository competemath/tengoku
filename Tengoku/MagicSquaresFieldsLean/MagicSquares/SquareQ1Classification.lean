import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.PrimeNegative
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.PrimePositive
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.QuadraticModels
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.Existence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares
open Certificates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- All seven positive cases below the center-zero square bound.
@isnad1 id=not.1h1v.s6.331eac873ca1 from=translated src=- shape=4da35102 vocab=b3d1e8b4
-/
theorem not_squareParker_of_card_q1_witness
    (hq : Fintype.card F ∈ ([29, 37, 41, 49, 53, 61, 73] : List ℕ)) : ¬ IsParker F := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq
  · letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_29⟩
  · letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_37⟩
  · letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_41⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field49 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 2).mp h) ⟨_, square_witness_49⟩
  · letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_53⟩
  · letI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_61⟩
  · letI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_73⟩

end MagicSquares
