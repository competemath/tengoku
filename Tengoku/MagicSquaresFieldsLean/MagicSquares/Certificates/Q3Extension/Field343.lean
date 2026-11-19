import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

local instance q3Extension343_prime : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def q3Extension343 : ExtensionSquareCertificate (ZMod 7) where
  modulus := [2, 0, 0, 1]
  entries := ⟨[0, 4, 2], [3, 2], [0, 1, 5], [1, 4, 3], [1], [1, 3, 4], [2, 6, 2], [6, 5], [2, 3, 5]⟩
  roots := ⟨[3, 2, 2], [5, 1, 2], [1, 1, 2], [2, 3, 2], [1], [6, 2], [4, 0, 2], [4, 2, 3], [5, 4, 1]⟩
  rootQuotients := ⟨[1, 4], [4, 4], [4, 4], [5, 4], [], [], [0, 4], [5, 2], [1, 1]⟩
  inverses := ![![[], [3, 5, 3], [4, 4, 5], [4, 6, 3], [5, 5, 2], [5, 0, 4], [4, 3, 4], [2, 0, 3], [6, 6, 1]],
    ![[4, 2, 4], [], [3, 5, 1], [1, 0, 5], [3, 4, 3], [1, 1, 6], [2, 2, 5], [5, 2, 5], [2, 0, 3]],
    ![[3, 3, 2], [4, 2, 6], [], [5, 5, 2], [5, 0, 4], [6, 1, 4], [6, 0, 2], [2, 2, 5], [4, 3, 4]],
    ![[3, 1, 4], [6, 0, 2], [2, 2, 5], [], [3, 3, 2], [5, 5, 1], [6, 1, 4], [1, 1, 6], [5, 0, 4]],
    ![[2, 2, 5], [4, 3, 4], [2, 0, 3], [4, 4, 5], [], [3, 3, 2], [5, 0, 4], [3, 4, 3], [5, 5, 2]],
    ![[2, 0, 3], [6, 6, 1], [1, 6, 3], [2, 2, 6], [4, 4, 5], [], [5, 5, 2], [1, 0, 5], [4, 6, 3]],
    ![[3, 4, 3], [5, 5, 2], [1, 0, 5], [1, 6, 3], [2, 0, 3], [2, 2, 5], [], [3, 5, 1], [4, 4, 5]],
    ![[5, 0, 4], [2, 5, 2], [5, 5, 2], [6, 6, 1], [4, 3, 4], [6, 0, 2], [4, 2, 6], [], [3, 5, 3]],
    ![[1, 1, 6], [5, 0, 4], [3, 4, 3], [2, 0, 3], [2, 2, 5], [3, 1, 4], [3, 3, 2], [4, 2, 4], []]]
  inverseQuotients := ![![[], [2, 6], [3, 6], [1, 4], [4, 4], [4, 6], [6], [4, 6], [4, 4]],
    ![[2, 6], [], [4, 2], [4, 6], [6], [4, 4], [4, 4], [6], [4, 6]],
    ![[3, 6], [4, 2], [], [4, 4], [4, 6], [0, 4], [4, 6], [4, 4], [6]],
    ![[1, 4], [4, 6], [4, 4], [], [3, 6], [3, 6], [0, 4], [4, 4], [4, 6]],
    ![[4, 4], [6], [4, 6], [3, 6], [], [3, 6], [4, 6], [6], [4, 4]],
    ![[4, 6], [4, 4], [0, 4], [3, 6], [3, 6], [], [4, 4], [4, 6], [1, 4]],
    ![[6], [4, 4], [4, 6], [0, 4], [4, 6], [4, 4], [], [4, 2], [3, 6]],
    ![[4, 6], [6], [4, 4], [4, 4], [6], [4, 6], [4, 2], [], [2, 6]],
    ![[4, 4], [4, 6], [6], [4, 6], [4, 4], [1, 4], [3, 6], [2, 6], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨true, [0, 0, 5], [0, 0, 1]⟩,
    ⟨false, [0, 6], [0, 4]⟩,
    ⟨true, [5], [1]⟩,
    ⟨false, [4], []⟩,
    ⟨true, [0, 2], []⟩,
    ⟨true, [6], [4]⟩,
    ⟨true, [0, 1], []⟩]

theorem q3Extension343_checked : q3Extension343.Valid := by
  decide +kernel

theorem q3Extension343_degree : (poly q3Extension343.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension343.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension343, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

theorem not_squareParker_of_card_343 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 343) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension343_checked q3Extension343_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
