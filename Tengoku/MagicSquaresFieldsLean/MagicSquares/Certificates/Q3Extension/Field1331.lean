import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.6208d772be9b from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension1331_prime : Fact (Nat.Prime 11) := ⟨by norm_num⟩

def q3Extension1331 : ExtensionSquareCertificate (ZMod 11) where
  modulus := [4, 1, 0, 1]
  entries := ⟨[5, 2], [8, 5, 9], [1, 4, 2], [8, 2, 2], [1], [5, 9, 9], [1, 7, 9], [5, 6, 2], [8, 9]⟩
  roots := ⟨[10, 9, 3], [4, 4, 3], [8, 3, 4], [5, 9, 1], [1], [7, 3], [3, 9, 5], [7, 0, 2], [0, 10, 1]⟩
  rootQuotients := ⟨[10, 9], [2, 9], [2, 5], [7, 1], [], [], [2, 3], [0, 4], [9, 1]⟩
  inverses := ![![[], [5, 4, 4], [6, 7, 8], [1, 6, 9], [5, 9, 1], [5, 1, 7], [0, 5, 7], [6, 10, 4], [8, 10, 6]],
    ![[6, 7, 7], [], [2, 8, 5], [3, 5, 2], [0, 6, 4], [3, 1, 5], [6, 2, 10], [0, 3, 2], [6, 10, 4]],
    ![[5, 4, 3], [9, 3, 6], [], [5, 9, 1], [5, 1, 7], [7, 8, 4], [8, 6, 9], [6, 2, 10], [0, 5, 7]],
    ![[10, 5, 2], [8, 6, 9], [6, 2, 10], [], [5, 4, 3], [8, 2, 7], [7, 8, 4], [3, 1, 5], [5, 1, 7]],
    ![[6, 2, 10], [0, 5, 7], [6, 10, 4], [6, 7, 8], [], [5, 4, 3], [5, 1, 7], [0, 6, 4], [5, 9, 1]],
    ![[6, 10, 4], [8, 10, 6], [4, 3, 7], [3, 9, 4], [6, 7, 8], [], [5, 9, 1], [3, 5, 2], [1, 6, 9]],
    ![[0, 6, 4], [5, 9, 1], [3, 5, 2], [4, 3, 7], [6, 10, 4], [6, 2, 10], [], [2, 8, 5], [6, 7, 8]],
    ![[5, 1, 7], [0, 8, 9], [5, 9, 1], [8, 10, 6], [0, 5, 7], [8, 6, 9], [9, 3, 6], [], [5, 4, 4]],
    ![[3, 1, 5], [5, 1, 7], [0, 6, 4], [6, 10, 4], [6, 2, 10], [10, 5, 2], [5, 4, 3], [6, 7, 7], []]]
  inverseQuotients := ![![[], [7, 8], [3, 6], [10, 4], [2], [8, 3], [8, 3], [8, 3], [2]],
    ![[7, 8], [], [6, 2], [8, 3], [8, 3], [2], [2], [8, 3], [8, 3]],
    ![[3, 6], [6, 2], [], [2], [8, 3], [1, 5], [8, 3], [2], [8, 3]],
    ![[10, 4], [8, 3], [2], [], [3, 6], [3, 6], [1, 5], [2], [8, 3]],
    ![[2], [8, 3], [8, 3], [3, 6], [], [3, 6], [8, 3], [8, 3], [2]],
    ![[8, 3], [2], [1, 5], [3, 6], [3, 6], [], [2], [8, 3], [10, 4]],
    ![[8, 3], [2], [8, 3], [1, 5], [8, 3], [2], [], [6, 2], [3, 6]],
    ![[8, 3], [8, 3], [2], [2], [8, 3], [8, 3], [6, 2], [], [7, 8]],
    ![[2], [8, 3], [8, 3], [8, 3], [2], [10, 4], [3, 6], [7, 8], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨true, [4, 1, 7], [10, 0, 1]⟩,
    ⟨false, [4, 7, 8], [3, 5]⟩,
    ⟨false, [8, 7, 5], [2, 9]⟩,
    ⟨true, [2, 10, 8], [5, 4, 3]⟩,
    ⟨true, [3, 0, 9], [2, 6, 9]⟩,
    ⟨false, [9, 6, 6], [0, 4]⟩,
    ⟨false, [2, 2, 9], [6, 3]⟩,
    ⟨true, [10], [3, 3, 4]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.bdb3d95e440b from=translated src=- shape=06f63001 vocab=07e512b5
-/
theorem q3Extension1331_checked : q3Extension1331.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.9bcb9aea1499 from=translated src=- shape=987d0d8b vocab=5337efee
-/
theorem q3Extension1331_degree : (poly q3Extension1331.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension1331.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension1331, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.95bb77520227 from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_1331 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 1331) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension1331_checked q3Extension1331_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
