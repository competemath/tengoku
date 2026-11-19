import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

local instance q3Extension103823_prime : Fact (Nat.Prime 47) := ⟨by norm_num⟩

def q3Extension103823 : ExtensionSquareCertificate (ZMod 47) where
  modulus := [4, 1, 0, 1]
  entries := ⟨[21, 8], [15, 15], [14, 24], [41, 16], [1], [8, 31], [35, 23], [34, 32], [28, 39]⟩
  roots := ⟨[45, 12, 15], [40, 23, 15], [7, 10, 21], [3, 18, 5], [1], [6, 25, 18], [24, 43, 11], [37, 1, 20], [28, 18, 17]⟩
  rootQuotients := ⟨[31, 37], [32, 37], [44, 18], [39, 25], [], [7, 42], [6, 27], [40, 24], [1, 7]⟩
  inverses := ![![[], [19, 21, 1], [23, 18, 21], [46, 36, 42], [1, 11, 5], [16, 35, 33], [12, 38, 13], [31, 12, 14], [24, 29, 26]],
    ![[28, 26, 46], [], [20, 32, 6], [39, 6, 7], [35, 9, 34], [23, 18, 21], [46, 36, 42], [41, 28, 17], [31, 12, 14]],
    ![[24, 29, 26], [27, 15, 41], [], [1, 11, 5], [16, 35, 33], [19, 21, 1], [8, 41, 40], [46, 36, 42], [12, 38, 13]],
    ![[1, 11, 5], [8, 41, 40], [46, 36, 42], [], [24, 29, 26], [12, 38, 13], [19, 21, 1], [23, 18, 21], [16, 35, 33]],
    ![[46, 36, 42], [12, 38, 13], [31, 12, 14], [23, 18, 21], [], [24, 29, 26], [16, 35, 33], [35, 9, 34], [1, 11, 5]],
    ![[31, 12, 14], [24, 29, 26], [28, 26, 46], [35, 9, 34], [23, 18, 21], [], [1, 11, 5], [39, 6, 7], [46, 36, 42]],
    ![[35, 9, 34], [1, 11, 5], [39, 6, 7], [28, 26, 46], [31, 12, 14], [46, 36, 42], [], [20, 32, 6], [23, 18, 21]],
    ![[16, 35, 33], [6, 19, 30], [1, 11, 5], [24, 29, 26], [12, 38, 13], [8, 41, 40], [27, 15, 41], [], [19, 21, 1]],
    ![[23, 18, 21], [16, 35, 33], [35, 9, 34], [31, 12, 14], [46, 36, 42], [1, 11, 5], [24, 29, 26], [28, 26, 46], []]]
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
    ⟨true, [43, 46], [1]⟩,
    ⟨false, [16, 8, 1], []⟩,
    ⟨false, [4, 1, 1], [16, 1]⟩,
    ⟨true, [15, 0, 2], [8, 2, 1]⟩,
    ⟨false, [37, 31, 9], [0, 4]⟩,
    ⟨true, [20, 35, 2], [42, 41, 34]⟩,
    ⟨false, [28, 22, 32], [46, 4]⟩,
    ⟨true, [21, 10, 5], [30, 45, 37]⟩,
    ⟨true, [35, 38, 32], [3, 6, 25]⟩,
    ⟨false, [4, 33, 28], [35, 37]⟩,
    ⟨false, [3, 27, 12], [15, 32]⟩,
    ⟨false, [2, 19, 46], [37, 3]⟩,
    ⟨true, [33, 35, 16], [27, 9, 1]⟩,
    ⟨true, [31, 36, 25], [4, 39, 21]⟩,
    ⟨true, [46], [12, 14, 14]⟩,
    ⟨true, [0, 1], []⟩]

theorem q3Extension103823_checked : q3Extension103823.Valid := by
  decide +kernel

theorem q3Extension103823_degree : (poly q3Extension103823.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension103823.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension103823, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

theorem not_squareParker_of_card_103823 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 103823) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension103823_checked q3Extension103823_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
