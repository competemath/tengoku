import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.ce7a50dc47fb from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension29791_prime : Fact (Nat.Prime 31) := ⟨by norm_num⟩

def q3Extension29791 : ExtensionSquareCertificate (ZMod 31) where
  modulus := [3, 0, 0, 1]
  entries := ⟨[3, 3], [24, 19], [7, 9], [5, 6], [1], [28, 25], [26, 22], [9, 12], [30, 28]⟩
  roots := ⟨[25, 16, 11], [22, 8, 7], [5, 25, 15], [23, 21, 14], [1], [10, 2, 6], [30, 7, 9], [13, 26, 5], [4, 11, 12]⟩
  rootQuotients := ⟨[11, 28], [19, 18], [6, 8], [30, 10], [], [24, 5], [2, 19], [12, 25], [16, 20]⟩
  inverses := ![![[], [5, 8, 19], [3, 11, 30], [6, 22, 29], [25, 9, 2], [29, 3, 11], [14, 10, 16], [2, 28, 20], [28, 20, 1]],
    ![[26, 23, 12], [], [23, 12, 13], [1, 14, 10], [17, 21, 15], [3, 11, 30], [6, 22, 29], [24, 26, 23], [2, 28, 20]],
    ![[28, 20, 1], [8, 19, 18], [], [25, 9, 2], [29, 3, 11], [5, 8, 19], [30, 17, 21], [6, 22, 29], [14, 10, 16]],
    ![[25, 9, 2], [30, 17, 21], [6, 22, 29], [], [28, 20, 1], [14, 10, 16], [5, 8, 19], [3, 11, 30], [29, 3, 11]],
    ![[6, 22, 29], [14, 10, 16], [2, 28, 20], [3, 11, 30], [], [28, 20, 1], [29, 3, 11], [17, 21, 15], [25, 9, 2]],
    ![[2, 28, 20], [28, 20, 1], [26, 23, 12], [17, 21, 15], [3, 11, 30], [], [25, 9, 2], [1, 14, 10], [6, 22, 29]],
    ![[17, 21, 15], [25, 9, 2], [1, 14, 10], [26, 23, 12], [2, 28, 20], [6, 22, 29], [], [23, 12, 13], [3, 11, 30]],
    ![[29, 3, 11], [7, 5, 8], [25, 9, 2], [28, 20, 1], [14, 10, 16], [30, 17, 21], [8, 19, 18], [], [5, 8, 19]],
    ![[3, 11, 30], [29, 3, 11], [17, 21, 15], [2, 28, 20], [6, 22, 29], [25, 9, 2], [28, 20, 1], [26, 23, 12], []]]
  inverseQuotients := ![![[], [6], [6], [6], [6], [6], [6], [6], [6]],
    ![[6], [], [6], [6], [6], [6], [6], [6], [6]],
    ![[6], [6], [], [6], [6], [6], [6], [6], [6]],
    ![[6], [6], [6], [], [6], [6], [6], [6], [6]],
    ![[6], [6], [6], [6], [], [6], [6], [6], [6]],
    ![[6], [6], [6], [6], [6], [], [6], [6], [6]],
    ![[6], [6], [6], [6], [6], [6], [], [6], [6]],
    ![[6], [6], [6], [6], [6], [6], [6], [], [6]],
    ![[6], [6], [6], [6], [6], [6], [6], [6], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨true, [28], [1]⟩,
    ⟨true, [0, 9], []⟩,
    ⟨false, [0, 0, 19], []⟩,
    ⟨true, [0, 0, 2], [0, 0, 20]⟩,
    ⟨false, [0, 19], [0, 4]⟩,
    ⟨false, [0, 0, 20], []⟩,
    ⟨false, [0, 9], [0, 28]⟩,
    ⟨true, [5], [19]⟩,
    ⟨false, [25], []⟩,
    ⟨true, [0, 5], []⟩,
    ⟨true, [18], [25]⟩,
    ⟨true, [0, 14], []⟩,
    ⟨true, [1], [10]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.5fedce524125 from=translated src=- shape=06f63001 vocab=8ade2ca6
-/
theorem q3Extension29791_checked : q3Extension29791.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.fbc2ec0c24ae from=translated src=- shape=987d0d8b vocab=1fb2a442
-/
theorem q3Extension29791_degree : (poly q3Extension29791.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension29791.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension29791, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.fe551d67f7f2 from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_29791 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 29791) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension29791_checked q3Extension29791_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
