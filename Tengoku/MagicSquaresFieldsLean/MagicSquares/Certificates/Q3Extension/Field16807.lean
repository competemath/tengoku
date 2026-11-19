import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

local instance q3Extension16807_prime : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def q3Extension16807 : ExtensionSquareCertificate (ZMod 7) where
  modulus := [3, 1, 0, 0, 0, 1]
  entries := ⟨[2, 1, 1], [0, 5, 5, 6], [1, 1, 1, 1], [0, 0, 0, 1], [1], [2, 0, 0, 6], [1, 6, 6, 6], [2, 2, 2, 1], [0, 6, 6]⟩
  roots := ⟨[4, 1], [4, 4, 0, 6, 3], [2, 3, 1, 5, 2], [5, 1, 1, 2, 1], [1], [0, 1, 2, 0, 2], [0, 1, 1, 0, 1], [5, 4, 0, 0, 3], [4, 0, 4, 3, 2]⟩
  rootQuotients := ⟨[], [3, 1, 1, 2], [1, 1, 6, 4], [6, 6, 4, 1], [], [4, 1, 0, 4], [2, 2, 0, 1], [3, 0, 0, 2], [3, 4, 5, 4]⟩
  inverses := ![![[], [6, 2, 1, 1, 3], [4, 2, 6, 2, 2], [6, 1, 6, 1, 4], [3, 0, 4, 3], [6, 4, 3, 0, 6], [5, 5, 6, 4, 3], [1, 3, 4, 0, 1], [5, 0, 2, 5]],
    ![[1, 5, 6, 6, 4], [], [3, 3, 4, 3, 1], [4, 5, 2, 0, 4], [2, 2, 1, 3, 4], [2, 0, 5, 2], [4, 0, 3, 4], [1, 1, 4, 5, 2], [1, 3, 4, 0, 1]],
    ![[3, 5, 1, 5, 5], [4, 4, 3, 4, 6], [], [3, 0, 4, 3], [6, 4, 3, 0, 6], [4, 1, 5], [3, 2, 5, 0, 3], [4, 0, 3, 4], [5, 5, 6, 4, 3]],
    ![[1, 6, 1, 6, 3], [3, 2, 5, 0, 3], [4, 0, 3, 4], [], [3, 5, 1, 5, 5], [5, 6, 4, 6, 6], [4, 1, 5], [2, 0, 5, 2], [6, 4, 3, 0, 6]],
    ![[4, 0, 3, 4], [5, 5, 6, 4, 3], [1, 3, 4, 0, 1], [4, 2, 6, 2, 2], [], [3, 5, 1, 5, 5], [6, 4, 3, 0, 6], [2, 2, 1, 3, 4], [3, 0, 4, 3]],
    ![[1, 3, 4, 0, 1], [5, 0, 2, 5], [3, 6, 2], [2, 1, 3, 1, 1], [4, 2, 6, 2, 2], [], [3, 0, 4, 3], [4, 5, 2, 0, 4], [6, 1, 6, 1, 4]],
    ![[2, 2, 1, 3, 4], [3, 0, 4, 3], [4, 5, 2, 0, 4], [3, 6, 2], [1, 3, 4, 0, 1], [4, 0, 3, 4], [], [3, 3, 4, 3, 1], [4, 2, 6, 2, 2]],
    ![[6, 4, 3, 0, 6], [6, 6, 3, 2, 5], [3, 0, 4, 3], [5, 0, 2, 5], [5, 5, 6, 4, 3], [3, 2, 5, 0, 3], [4, 4, 3, 4, 6], [], [6, 2, 1, 1, 3]],
    ![[2, 0, 5, 2], [6, 4, 3, 0, 6], [2, 2, 1, 3, 4], [1, 3, 4, 0, 1], [4, 0, 3, 4], [1, 6, 1, 6, 3], [3, 5, 1, 5, 5], [1, 5, 6, 6, 4], []]]
  inverseQuotients := ![![[], [6, 3, 3], [1, 5, 5], [6, 3, 3], [3], [2, 6, 6], [6, 3, 3], [2, 6, 6], [3]],
    ![[6, 3, 3], [], [1, 5, 5], [2, 6, 6], [6, 3, 3], [3], [3], [6, 3, 3], [2, 6, 6]],
    ![[1, 5, 5], [1, 5, 5], [], [3], [2, 6, 6], [3], [2, 6, 6], [3], [6, 3, 3]],
    ![[6, 3, 3], [2, 6, 6], [3], [], [1, 5, 5], [1, 5, 5], [3], [3], [2, 6, 6]],
    ![[3], [6, 3, 3], [2, 6, 6], [1, 5, 5], [], [1, 5, 5], [2, 6, 6], [6, 3, 3], [3]],
    ![[2, 6, 6], [3], [3], [1, 5, 5], [1, 5, 5], [], [3], [2, 6, 6], [6, 3, 3]],
    ![[6, 3, 3], [3], [2, 6, 6], [3], [2, 6, 6], [3], [], [1, 5, 5], [1, 5, 5]],
    ![[2, 6, 6], [6, 3, 3], [3], [3], [6, 3, 3], [2, 6, 6], [1, 5, 5], [], [6, 3, 3]],
    ![[3], [2, 6, 6], [6, 3, 3], [2, 6, 6], [3], [6, 3, 3], [1, 5, 5], [6, 3, 3], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨false, [0, 0, 0, 0, 1], []⟩,
    ⟨false, [0, 0, 0, 4, 6], [0, 0, 0, 1]⟩,
    ⟨false, [0, 1, 1, 5, 6], [0, 2, 6, 1]⟩,
    ⟨false, [4, 0, 1, 2, 3], [1, 2, 4, 1]⟩,
    ⟨true, [1, 2, 1, 4, 5], [2, 4, 3, 5, 2]⟩,
    ⟨true, [1, 6, 3, 0, 2], [2, 0, 5, 5, 4]⟩,
    ⟨false, [6, 1, 2, 3, 2], [3, 5, 0, 4]⟩,
    ⟨true, [1, 0, 1, 0, 2], [2, 2, 3, 5, 4]⟩,
    ⟨false, [1, 2, 5, 2, 1], [0, 4, 0, 4]⟩,
    ⟨false, [6, 1, 2, 3, 6], [3, 0, 4, 1]⟩,
    ⟨true, [2, 2, 1, 3, 1], [4, 3, 5, 1, 1]⟩,
    ⟨true, [1], [2, 3, 4, 6, 1]⟩,
    ⟨true, [0, 1], []⟩]

theorem q3Extension16807_checked : q3Extension16807.Valid := by
  decide +kernel

theorem q3Extension16807_degree : (poly q3Extension16807.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension16807.modulus).coeff 5 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension16807, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

theorem not_squareParker_of_card_16807 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 16807) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 5)
    q3Extension16807_checked q3Extension16807_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
