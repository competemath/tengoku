import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.PrimeNegative
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.PrimePositive
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.Cubes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MagicSquares
open Certificates

local instance fastDecidablePrime (n : ℕ) : Decidable n.Prime := Nat.decidablePrime' n

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- Explicit positive certificates cover every other odd prime below 1037.-/
theorem not_cubeParker_of_card_prime_witness
    (hq : Fintype.card F ∈ ([11, 17, 23, 29, 41, 47, 53, 59, 71, 73, 83, 89, 97, 101, 103, 107, 109, 113, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033] : List ℕ)) : ¬ IsNParker F 3 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
  · letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_11⟩
  · letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_17⟩
  · letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_23⟩
  · letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_29⟩
  · letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_41⟩
  · letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_47⟩
  · letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_53⟩
  · letI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_59⟩
  · letI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_71⟩
  · letI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_73⟩
  · letI : Fact (Nat.Prime 83) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_83⟩
  · letI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_89⟩
  · letI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_97⟩
  · letI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_101⟩
  · letI : Fact (Nat.Prime 103) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_103⟩
  · letI : Fact (Nat.Prime 107) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_107⟩
  · letI : Fact (Nat.Prime 109) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_109⟩
  · letI : Fact (Nat.Prime 113) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_113⟩
  · letI : Fact (Nat.Prime 131) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_131⟩
  · letI : Fact (Nat.Prime 137) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_137⟩
  · letI : Fact (Nat.Prime 139) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_139⟩
  · letI : Fact (Nat.Prime 149) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_149⟩
  · letI : Fact (Nat.Prime 151) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_151⟩
  · letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_157⟩
  · letI : Fact (Nat.Prime 163) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_163⟩
  · letI : Fact (Nat.Prime 167) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_167⟩
  · letI : Fact (Nat.Prime 173) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_173⟩
  · letI : Fact (Nat.Prime 179) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_179⟩
  · letI : Fact (Nat.Prime 181) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_181⟩
  · letI : Fact (Nat.Prime 191) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_191⟩
  · letI : Fact (Nat.Prime 193) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_193⟩
  · letI : Fact (Nat.Prime 197) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_197⟩
  · letI : Fact (Nat.Prime 199) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_199⟩
  · letI : Fact (Nat.Prime 211) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_211⟩
  · letI : Fact (Nat.Prime 223) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_223⟩
  · letI : Fact (Nat.Prime 227) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_227⟩
  · letI : Fact (Nat.Prime 229) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_229⟩
  · letI : Fact (Nat.Prime 233) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_233⟩
  · letI : Fact (Nat.Prime 239) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_239⟩
  · letI : Fact (Nat.Prime 241) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_241⟩
  · letI : Fact (Nat.Prime 251) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_251⟩
  · letI : Fact (Nat.Prime 257) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_257⟩
  · letI : Fact (Nat.Prime 263) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_263⟩
  · letI : Fact (Nat.Prime 269) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_269⟩
  · letI : Fact (Nat.Prime 271) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_271⟩
  · letI : Fact (Nat.Prime 277) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_277⟩
  · letI : Fact (Nat.Prime 281) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_281⟩
  · letI : Fact (Nat.Prime 283) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_283⟩
  · letI : Fact (Nat.Prime 293) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_293⟩
  · letI : Fact (Nat.Prime 307) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_307⟩
  · letI : Fact (Nat.Prime 311) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_311⟩
  · letI : Fact (Nat.Prime 313) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_313⟩
  · letI : Fact (Nat.Prime 317) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_317⟩
  · letI : Fact (Nat.Prime 331) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_331⟩
  · letI : Fact (Nat.Prime 337) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_337⟩
  · letI : Fact (Nat.Prime 347) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_347⟩
  · letI : Fact (Nat.Prime 349) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_349⟩
  · letI : Fact (Nat.Prime 353) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_353⟩
  · letI : Fact (Nat.Prime 359) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_359⟩
  · letI : Fact (Nat.Prime 367) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_367⟩
  · letI : Fact (Nat.Prime 373) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_373⟩
  · letI : Fact (Nat.Prime 379) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_379⟩
  · letI : Fact (Nat.Prime 383) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_383⟩
  · letI : Fact (Nat.Prime 389) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_389⟩
  · letI : Fact (Nat.Prime 397) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_397⟩
  · letI : Fact (Nat.Prime 401) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_401⟩
  · letI : Fact (Nat.Prime 409) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_409⟩
  · letI : Fact (Nat.Prime 419) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_419⟩
  · letI : Fact (Nat.Prime 421) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_421⟩
  · letI : Fact (Nat.Prime 431) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_431⟩
  · letI : Fact (Nat.Prime 433) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_433⟩
  · letI : Fact (Nat.Prime 439) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_439⟩
  · letI : Fact (Nat.Prime 443) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_443⟩
  · letI : Fact (Nat.Prime 449) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_449⟩
  · letI : Fact (Nat.Prime 457) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_457⟩
  · letI : Fact (Nat.Prime 461) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_461⟩
  · letI : Fact (Nat.Prime 463) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_463⟩
  · letI : Fact (Nat.Prime 467) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_467⟩
  · letI : Fact (Nat.Prime 479) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_479⟩
  · letI : Fact (Nat.Prime 487) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_487⟩
  · letI : Fact (Nat.Prime 491) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_491⟩
  · letI : Fact (Nat.Prime 499) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_499⟩
  · letI : Fact (Nat.Prime 503) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_503⟩
  · letI : Fact (Nat.Prime 509) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_509⟩
  · letI : Fact (Nat.Prime 521) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_521⟩
  · letI : Fact (Nat.Prime 523) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_523⟩
  · letI : Fact (Nat.Prime 541) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_541⟩
  · letI : Fact (Nat.Prime 547) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_547⟩
  · letI : Fact (Nat.Prime 557) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_557⟩
  · letI : Fact (Nat.Prime 563) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_563⟩
  · letI : Fact (Nat.Prime 569) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_569⟩
  · letI : Fact (Nat.Prime 571) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_571⟩
  · letI : Fact (Nat.Prime 577) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_577⟩
  · letI : Fact (Nat.Prime 587) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_587⟩
  · letI : Fact (Nat.Prime 593) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_593⟩
  · letI : Fact (Nat.Prime 599) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_599⟩
  · letI : Fact (Nat.Prime 601) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_601⟩
  · letI : Fact (Nat.Prime 607) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_607⟩
  · letI : Fact (Nat.Prime 613) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_613⟩
  · letI : Fact (Nat.Prime 617) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_617⟩
  · letI : Fact (Nat.Prime 619) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_619⟩
  · letI : Fact (Nat.Prime 631) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_631⟩
  · letI : Fact (Nat.Prime 641) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_641⟩
  · letI : Fact (Nat.Prime 643) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_643⟩
  · letI : Fact (Nat.Prime 647) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_647⟩
  · letI : Fact (Nat.Prime 653) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_653⟩
  · letI : Fact (Nat.Prime 659) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_659⟩
  · letI : Fact (Nat.Prime 661) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_661⟩
  · letI : Fact (Nat.Prime 673) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_673⟩
  · letI : Fact (Nat.Prime 677) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_677⟩
  · letI : Fact (Nat.Prime 683) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_683⟩
  · letI : Fact (Nat.Prime 691) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_691⟩
  · letI : Fact (Nat.Prime 701) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_701⟩
  · letI : Fact (Nat.Prime 709) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_709⟩
  · letI : Fact (Nat.Prime 719) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_719⟩
  · letI : Fact (Nat.Prime 727) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_727⟩
  · letI : Fact (Nat.Prime 733) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_733⟩
  · letI : Fact (Nat.Prime 739) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_739⟩
  · letI : Fact (Nat.Prime 743) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_743⟩
  · letI : Fact (Nat.Prime 751) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_751⟩
  · letI : Fact (Nat.Prime 757) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_757⟩
  · letI : Fact (Nat.Prime 761) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_761⟩
  · letI : Fact (Nat.Prime 769) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_769⟩
  · letI : Fact (Nat.Prime 773) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_773⟩
  · letI : Fact (Nat.Prime 787) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_787⟩
  · letI : Fact (Nat.Prime 797) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_797⟩
  · letI : Fact (Nat.Prime 809) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_809⟩
  · letI : Fact (Nat.Prime 811) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_811⟩
  · letI : Fact (Nat.Prime 821) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_821⟩
  · letI : Fact (Nat.Prime 823) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_823⟩
  · letI : Fact (Nat.Prime 827) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_827⟩
  · letI : Fact (Nat.Prime 829) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_829⟩
  · letI : Fact (Nat.Prime 839) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_839⟩
  · letI : Fact (Nat.Prime 853) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_853⟩
  · letI : Fact (Nat.Prime 857) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_857⟩
  · letI : Fact (Nat.Prime 859) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_859⟩
  · letI : Fact (Nat.Prime 863) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_863⟩
  · letI : Fact (Nat.Prime 877) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_877⟩
  · letI : Fact (Nat.Prime 881) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_881⟩
  · letI : Fact (Nat.Prime 883) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_883⟩
  · letI : Fact (Nat.Prime 887) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_887⟩
  · letI : Fact (Nat.Prime 907) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_907⟩
  · letI : Fact (Nat.Prime 911) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_911⟩
  · letI : Fact (Nat.Prime 919) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_919⟩
  · letI : Fact (Nat.Prime 929) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_929⟩
  · letI : Fact (Nat.Prime 937) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_937⟩
  · letI : Fact (Nat.Prime 941) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_941⟩
  · letI : Fact (Nat.Prime 947) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_947⟩
  · letI : Fact (Nat.Prime 953) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_953⟩
  · letI : Fact (Nat.Prime 967) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_967⟩
  · letI : Fact (Nat.Prime 971) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_971⟩
  · letI : Fact (Nat.Prime 977) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_977⟩
  · letI : Fact (Nat.Prime 983) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_983⟩
  · letI : Fact (Nat.Prime 991) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_991⟩
  · letI : Fact (Nat.Prime 997) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_997⟩
  · letI : Fact (Nat.Prime 1009) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_1009⟩
  · letI : Fact (Nat.Prime 1013) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_1013⟩
  · letI : Fact (Nat.Prime 1019) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_1019⟩
  · letI : Fact (Nat.Prime 1021) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_1021⟩
  · letI : Fact (Nat.Prime 1031) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_1031⟩
  · letI : Fact (Nat.Prime 1033) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 3).mp h) ⟨_, cube_witness_1033⟩

end MagicSquares
