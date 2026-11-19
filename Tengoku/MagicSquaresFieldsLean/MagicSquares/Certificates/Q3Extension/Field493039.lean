import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.0f260b9d0b2c from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension493039_prime : Fact (Nat.Prime 79) := ⟨by norm_num⟩

def q3Extension493039 : ExtensionSquareCertificate (ZMod 79) where
  modulus := [2, 0, 0, 1]
  entries := ⟨[25, 6], [63, 55], [73, 18], [49, 12], [1], [32, 67], [8, 61], [18, 24], [56, 73]⟩
  roots := ⟨[73, 41, 15], [65, 32, 14], [54, 69, 2], [21, 77, 30], [1], [33, 6, 21], [54, 67, 25], [2, 37, 33], [10, 57, 39]⟩
  rootQuotients := ⟨[45, 67], [27, 38], [39, 4], [38, 31], [], [15, 46], [32, 72], [72, 62], [22, 20]⟩
  inverses := ![![[], [61, 44, 68], [45, 48, 67], [11, 17, 55], [68, 62, 24], [49, 47, 8], [17, 55, 6], [30, 32, 71], [34, 31, 12]],
    ![[18, 35, 11], [], [58, 25, 53], [15, 16, 75], [62, 24, 73], [45, 48, 67], [11, 17, 55], [31, 12, 76], [30, 32, 71]],
    ![[34, 31, 12], [21, 54, 26], [], [68, 62, 24], [49, 47, 8], [61, 44, 68], [64, 63, 4], [11, 17, 55], [17, 55, 6]],
    ![[68, 62, 24], [64, 63, 4], [11, 17, 55], [], [34, 31, 12], [17, 55, 6], [61, 44, 68], [45, 48, 67], [49, 47, 8]],
    ![[11, 17, 55], [17, 55, 6], [30, 32, 71], [45, 48, 67], [], [34, 31, 12], [49, 47, 8], [62, 24, 73], [68, 62, 24]],
    ![[30, 32, 71], [34, 31, 12], [18, 35, 11], [62, 24, 73], [45, 48, 67], [], [68, 62, 24], [15, 16, 75], [11, 17, 55]],
    ![[62, 24, 73], [68, 62, 24], [15, 16, 75], [18, 35, 11], [30, 32, 71], [11, 17, 55], [], [58, 25, 53], [45, 48, 67]],
    ![[49, 47, 8], [48, 67, 3], [68, 62, 24], [34, 31, 12], [17, 55, 6], [64, 63, 4], [21, 54, 26], [], [61, 44, 68]],
    ![[45, 48, 67], [49, 47, 8], [62, 24, 73], [30, 32, 71], [11, 17, 55], [68, 62, 24], [34, 31, 12], [18, 35, 11], []]]
  inverseQuotients := ![![[], [65], [65], [65], [65], [65], [65], [65], [65]],
    ![[65], [], [65], [65], [65], [65], [65], [65], [65]],
    ![[65], [65], [], [65], [65], [65], [65], [65], [65]],
    ![[65], [65], [65], [], [65], [65], [65], [65], [65]],
    ![[65], [65], [65], [65], [], [65], [65], [65], [65]],
    ![[65], [65], [65], [65], [65], [], [65], [65], [65]],
    ![[65], [65], [65], [65], [65], [65], [], [65], [65]],
    ![[65], [65], [65], [65], [65], [65], [65], [], [65]],
    ![[65], [65], [65], [65], [65], [65], [65], [65], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨true, [77], [1]⟩,
    ⟨true, [0, 4], []⟩,
    ⟨true, [47], [16]⟩,
    ⟨false, [76], []⟩,
    ⟨false, [9], []⟩,
    ⟨false, [2], []⟩,
    ⟨false, [4], []⟩,
    ⟨true, [0, 16], []⟩,
    ⟨false, [0, 0, 19], []⟩,
    ⟨true, [0, 0, 68], [0, 0, 45]⟩,
    ⟨true, [0, 0, 74], [0, 0, 42]⟩,
    ⟨true, [0, 0, 29], [0, 0, 25]⟩,
    ⟨true, [0, 0, 56], [0, 0, 51]⟩,
    ⟨false, [0, 48], [0, 55]⟩,
    ⟨true, [53], [13]⟩,
    ⟨true, [0, 44], []⟩,
    ⟨true, [78], [40]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.5d808f00e0c8 from=translated src=- shape=06f63001 vocab=82c8efa2
-/
theorem q3Extension493039_checked : q3Extension493039.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.27938b0be1bc from=translated src=- shape=987d0d8b vocab=d7fa1f47
-/
theorem q3Extension493039_degree : (poly q3Extension493039.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension493039.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension493039, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.dff6f22a39fd from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_493039 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 493039) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension493039_checked q3Extension493039_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
