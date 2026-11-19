import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

local instance q3Extension300763_prime : Fact (Nat.Prime 67) := ⟨by norm_num⟩

def q3Extension300763 : ExtensionSquareCertificate (ZMod 67) where
  modulus := [2, 0, 0, 1]
  entries := ⟨[32, 2], [11, 59], [27, 6], [63, 4], [1], [6, 63], [42, 61], [58, 8], [37, 65]⟩
  roots := ⟨[58, 42, 31], [19, 15, 17], [31, 22, 3], [64, 42, 26], [1], [42, 30, 18], [60, 11, 23], [61, 29, 31], [37, 25, 16]⟩
  rootQuotients := ⟨[58, 23], [41, 21], [65, 9], [40, 6], [], [8, 56], [37, 60], [56, 23], [63, 55]⟩
  inverses := ![![[], [23, 5, 4], [43, 21, 57], [19, 42, 47], [48, 25, 20], [16, 53, 29], [12, 23, 5], [51, 14, 38], [24, 46, 10]],
    ![[44, 62, 63], [], [41, 6, 45], [59, 7, 19], [55, 44, 62], [43, 21, 57], [19, 42, 47], [61, 22, 31], [51, 14, 38]],
    ![[24, 46, 10], [26, 61, 22], [], [48, 25, 20], [16, 53, 29], [23, 5, 4], [8, 60, 48], [19, 42, 47], [12, 23, 5]],
    ![[48, 25, 20], [8, 60, 48], [19, 42, 47], [], [24, 46, 10], [12, 23, 5], [23, 5, 4], [43, 21, 57], [16, 53, 29]],
    ![[19, 42, 47], [12, 23, 5], [51, 14, 38], [43, 21, 57], [], [24, 46, 10], [16, 53, 29], [55, 44, 62], [48, 25, 20]],
    ![[51, 14, 38], [24, 46, 10], [44, 62, 63], [55, 44, 62], [43, 21, 57], [], [48, 25, 20], [59, 7, 19], [19, 42, 47]],
    ![[55, 44, 62], [48, 25, 20], [59, 7, 19], [44, 62, 63], [51, 14, 38], [19, 42, 47], [], [41, 6, 45], [43, 21, 57]],
    ![[16, 53, 29], [6, 45, 36], [48, 25, 20], [24, 46, 10], [12, 23, 5], [8, 60, 48], [26, 61, 22], [], [23, 5, 4]],
    ![[43, 21, 57], [16, 53, 29], [55, 44, 62], [51, 14, 38], [19, 42, 47], [48, 25, 20], [24, 46, 10], [44, 62, 63], []]]
  inverseQuotients := ![![[], [40], [40], [40], [40], [40], [40], [40], [40]],
    ![[40], [], [40], [40], [40], [40], [40], [40], [40]],
    ![[40], [40], [], [40], [40], [40], [40], [40], [40]],
    ![[40], [40], [40], [], [40], [40], [40], [40], [40]],
    ![[40], [40], [40], [40], [], [40], [40], [40], [40]],
    ![[40], [40], [40], [40], [40], [], [40], [40], [40]],
    ![[40], [40], [40], [40], [40], [40], [], [40], [40]],
    ![[40], [40], [40], [40], [40], [40], [40], [], [40]],
    ![[40], [40], [40], [40], [40], [40], [40], [40], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨false, [0, 65], [0, 1]⟩,
    ⟨true, [59], [4]⟩,
    ⟨false, [64], []⟩,
    ⟨false, [9], []⟩,
    ⟨true, [0, 14], []⟩,
    ⟨false, [0, 0, 62], []⟩,
    ⟨true, [0, 0, 17], [0, 0, 25]⟩,
    ⟨true, [0, 0, 25], [0, 0, 21]⟩,
    ⟨false, [0, 23], [0, 22]⟩,
    ⟨true, [14], [60]⟩,
    ⟨true, [0, 62], []⟩,
    ⟨false, [0, 0, 25], []⟩,
    ⟨true, [0, 0, 23], [0, 0, 22]⟩,
    ⟨true, [0, 0, 14], [0, 0, 60]⟩,
    ⟨false, [0, 10], [0, 62]⟩,
    ⟨true, [1], [33]⟩,
    ⟨true, [0, 1], []⟩]

theorem q3Extension300763_checked : q3Extension300763.Valid := by
  decide +kernel

theorem q3Extension300763_degree : (poly q3Extension300763.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension300763.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension300763, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

theorem not_squareParker_of_card_300763 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 300763) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension300763_checked q3Extension300763_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
