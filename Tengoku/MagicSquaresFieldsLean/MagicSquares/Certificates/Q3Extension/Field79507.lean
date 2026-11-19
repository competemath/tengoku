import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

local instance q3Extension79507_prime : Fact (Nat.Prime 43) := ⟨by norm_num⟩

def q3Extension79507 : ExtensionSquareCertificate (ZMod 43) where
  modulus := [3, 0, 0, 1]
  entries := ⟨[1, 16, 1], [1, 22, 39], [1, 5, 3], [1, 32, 2], [1], [1, 11, 41], [1, 38, 40], [1, 21, 4], [1, 27, 42]⟩
  roots := ⟨[35, 12, 17], [20, 39, 21], [3, 30, 1], [21, 24, 15], [1], [42, 16], [39, 8, 3], [10, 26, 18], [29, 9, 6]⟩
  rootQuotients := ⟨[21, 31], [4, 11], [17, 1], [32, 10], [], [], [5, 9], [33, 23], [22, 36]⟩
  inverses := ![![[], [34, 14, 38], [1, 8, 34], [2, 16, 25], [41, 27, 18], [28, 9, 6], [21, 39, 26], [15, 34, 37], [42, 35, 9]],
    ![[9, 29, 5], [], [31, 33, 22], [29, 17, 40], [22, 4, 17], [1, 8, 34], [2, 16, 25], [11, 2, 30], [15, 34, 37]],
    ![[42, 35, 9], [12, 10, 21], [], [41, 27, 18], [28, 9, 6], [34, 14, 38], [14, 26, 3], [2, 16, 25], [21, 39, 26]],
    ![[41, 27, 18], [14, 26, 3], [2, 16, 25], [], [42, 35, 9], [21, 39, 26], [34, 14, 38], [1, 8, 34], [28, 9, 6]],
    ![[2, 16, 25], [21, 39, 26], [15, 34, 37], [1, 8, 34], [], [42, 35, 9], [28, 9, 6], [22, 4, 17], [41, 27, 18]],
    ![[15, 34, 37], [42, 35, 9], [9, 29, 5], [22, 4, 17], [1, 8, 34], [], [41, 27, 18], [29, 17, 40], [2, 16, 25]],
    ![[22, 4, 17], [41, 27, 18], [29, 17, 40], [9, 29, 5], [15, 34, 37], [2, 16, 25], [], [31, 33, 22], [1, 8, 34]],
    ![[28, 9, 6], [32, 41, 13], [41, 27, 18], [42, 35, 9], [21, 39, 26], [14, 26, 3], [12, 10, 21], [], [34, 14, 38]],
    ![[1, 8, 34], [28, 9, 6], [22, 4, 17], [15, 34, 37], [2, 16, 25], [41, 27, 18], [42, 35, 9], [9, 29, 5], []]]
  inverseQuotients := ![![[], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18]],
    ![[14, 18], [], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18]],
    ![[14, 18], [14, 18], [], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18]],
    ![[14, 18], [14, 18], [14, 18], [], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18]],
    ![[14, 18], [14, 18], [14, 18], [14, 18], [], [14, 18], [14, 18], [14, 18], [14, 18]],
    ![[14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [], [14, 18], [14, 18], [14, 18]],
    ![[14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [], [14, 18], [14, 18]],
    ![[14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [], [14, 18]],
    ![[14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], [14, 18], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨false, [0, 40], [0, 1]⟩,
    ⟨true, [16], [9]⟩,
    ⟨true, [0, 41], []⟩,
    ⟨false, [0, 0, 4], []⟩,
    ⟨true, [0, 0, 38], [0, 0, 16]⟩,
    ⟨true, [0, 0, 11], [0, 0, 25]⟩,
    ⟨false, [0, 24], [0, 35]⟩,
    ⟨true, [35], [17]⟩,
    ⟨false, [21], []⟩,
    ⟨false, [11], []⟩,
    ⟨true, [0, 35], []⟩,
    ⟨false, [0, 0, 21], []⟩,
    ⟨false, [0, 10], [0, 11]⟩,
    ⟨true, [1], [14]⟩,
    ⟨true, [0, 1], []⟩]

theorem q3Extension79507_checked : q3Extension79507.Valid := by
  decide +kernel

theorem q3Extension79507_degree : (poly q3Extension79507.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension79507.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension79507, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

theorem not_squareParker_of_card_79507 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 79507) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension79507_checked q3Extension79507_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
