import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

local instance q3Extension205379_prime : Fact (Nat.Prime 59) := ⟨by norm_num⟩

def q3Extension205379 : ExtensionSquareCertificate (ZMod 59) where
  modulus := [1, 1, 0, 1]
  entries := ⟨[6, 8], [40, 27], [16, 24], [11, 16], [1], [50, 43], [45, 35], [21, 32], [55, 51]⟩
  roots := ⟨[15, 29, 17], [7, 50, 29], [0, 13, 13], [39, 38, 9], [1], [50, 45, 1], [28, 48, 12], [44, 51, 2], [36, 19, 28]⟩
  rootQuotients := ⟨[42, 53], [9, 15], [43, 51], [35, 22], [], [31, 1], [31, 26], [27, 4], [2, 17]⟩
  inverses := ![![[], [14, 1, 22], [24, 27, 4], [48, 54, 8], [11, 5, 51], [43, 41, 17], [47, 16, 57], [16, 18, 42], [35, 32, 55]],
    ![[45, 58, 37], [], [49, 33, 18], [8, 9, 21], [12, 43, 2], [24, 27, 4], [48, 54, 8], [6, 51, 1], [16, 18, 42]],
    ![[35, 32, 55], [10, 26, 41], [], [11, 5, 51], [43, 41, 17], [14, 1, 22], [51, 50, 38], [48, 54, 8], [47, 16, 57]],
    ![[11, 5, 51], [51, 50, 38], [48, 54, 8], [], [35, 32, 55], [47, 16, 57], [14, 1, 22], [24, 27, 4], [43, 41, 17]],
    ![[48, 54, 8], [47, 16, 57], [16, 18, 42], [24, 27, 4], [], [35, 32, 55], [43, 41, 17], [12, 43, 2], [11, 5, 51]],
    ![[16, 18, 42], [35, 32, 55], [45, 58, 37], [12, 43, 2], [24, 27, 4], [], [11, 5, 51], [8, 9, 21], [48, 54, 8]],
    ![[12, 43, 2], [11, 5, 51], [8, 9, 21], [45, 58, 37], [16, 18, 42], [48, 54, 8], [], [49, 33, 18], [24, 27, 4]],
    ![[43, 41, 17], [53, 8, 58], [11, 5, 51], [35, 32, 55], [47, 16, 57], [51, 50, 38], [10, 26, 41], [], [14, 1, 22]],
    ![[24, 27, 4], [43, 41, 17], [12, 43, 2], [16, 18, 42], [48, 54, 8], [11, 5, 51], [35, 32, 55], [45, 58, 37], []]]
  inverseQuotients := ![![[], [54], [54], [54], [54], [54], [54], [54], [54]],
    ![[54], [], [54], [54], [54], [54], [54], [54], [54]],
    ![[54], [54], [], [54], [54], [54], [54], [54], [54]],
    ![[54], [54], [54], [], [54], [54], [54], [54], [54]],
    ![[54], [54], [54], [54], [], [54], [54], [54], [54]],
    ![[54], [54], [54], [54], [54], [], [54], [54], [54]],
    ![[54], [54], [54], [54], [54], [54], [], [54], [54]],
    ![[54], [54], [54], [54], [54], [54], [54], [], [54]],
    ![[54], [54], [54], [54], [54], [54], [54], [54], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨true, [58, 58], [1]⟩,
    ⟨false, [1, 2, 1], []⟩,
    ⟨false, [56, 58, 5], [4, 1]⟩,
    ⟨true, [54, 14, 50], [5, 49, 25]⟩,
    ⟨false, [41, 31, 28], [43, 22]⟩,
    ⟨false, [4, 22, 54], [25, 17]⟩,
    ⟨false, [0, 17, 6], [16, 25]⟩,
    ⟨true, [42, 15, 55], [17, 27, 36]⟩,
    ⟨false, [55, 7, 50], [57, 16]⟩,
    ⟨false, [24, 48, 40], [51, 22]⟩,
    ⟨true, [31, 12, 50], [28, 5, 7]⟩,
    ⟨false, [56, 53, 36], [20, 22]⟩,
    ⟨false, [28, 57, 58], [40, 57]⟩,
    ⟨false, [13, 1, 6], [4, 1]⟩,
    ⟨false, [39, 37, 3], [12, 36]⟩,
    ⟨true, [58], [1, 45, 9]⟩,
    ⟨true, [0, 1], []⟩]

theorem q3Extension205379_checked : q3Extension205379.Valid := by
  decide +kernel

theorem q3Extension205379_degree : (poly q3Extension205379.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension205379.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension205379, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

theorem not_squareParker_of_card_205379 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 205379) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension205379_checked q3Extension205379_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
