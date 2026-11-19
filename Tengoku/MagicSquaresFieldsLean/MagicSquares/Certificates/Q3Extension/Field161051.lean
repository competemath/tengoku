import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.6208d772be9b from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension161051_prime : Fact (Nat.Prime 11) := ⟨by norm_num⟩

def q3Extension161051 : ExtensionSquareCertificate (ZMod 11) where
  modulus := [2, 0, 0, 0, 0, 1]
  entries := ⟨[1, 0, 0, 1], [1, 0, 0, 7], [1, 0, 0, 3], [1, 0, 0, 2], [1], [1, 0, 0, 9], [1, 0, 0, 8], [1, 0, 0, 4], [1, 0, 0, 10]⟩
  roots := ⟨[3, 0, 4, 6, 1], [4, 1, 8, 4, 2], [3, 0, 5, 7, 5], [7, 8, 5, 2, 3], [1], [3, 0, 9, 10, 3], [7, 7, 4, 8, 5], [8, 0, 10, 9, 2], [7, 2, 1, 10, 1]⟩
  rootQuotients := ⟨[4, 0, 1, 1], [2, 4, 5, 4], [4, 0, 4, 3], [2, 1, 1, 9], [], [4, 0, 5, 9], [2, 5, 3, 3], [4, 0, 3, 4], [2, 3, 9, 1]⟩
  inverses := ![![[], [0, 0, 1], [0, 0, 3], [0, 0, 6], [0, 0, 5], [0, 0, 9], [0, 0, 4], [0, 0, 2], [0, 0, 8]],
    ![[0, 0, 10], [], [0, 0, 4], [0, 0, 1], [0, 0, 7], [0, 0, 3], [0, 0, 6], [0, 0, 9], [0, 0, 2]],
    ![[0, 0, 8], [0, 0, 7], [], [0, 0, 5], [0, 0, 9], [0, 0, 1], [0, 0, 10], [0, 0, 6], [0, 0, 4]],
    ![[0, 0, 5], [0, 0, 10], [0, 0, 6], [], [0, 0, 8], [0, 0, 4], [0, 0, 1], [0, 0, 3], [0, 0, 9]],
    ![[0, 0, 6], [0, 0, 4], [0, 0, 2], [0, 0, 3], [], [0, 0, 8], [0, 0, 9], [0, 0, 7], [0, 0, 5]],
    ![[0, 0, 2], [0, 0, 8], [0, 0, 10], [0, 0, 7], [0, 0, 3], [], [0, 0, 5], [0, 0, 1], [0, 0, 6]],
    ![[0, 0, 7], [0, 0, 5], [0, 0, 1], [0, 0, 10], [0, 0, 2], [0, 0, 6], [], [0, 0, 4], [0, 0, 3]],
    ![[0, 0, 9], [0, 0, 2], [0, 0, 5], [0, 0, 8], [0, 0, 4], [0, 0, 10], [0, 0, 7], [], [0, 0, 1]],
    ![[0, 0, 3], [0, 0, 9], [0, 0, 7], [0, 0, 2], [0, 0, 6], [0, 0, 5], [0, 0, 8], [0, 0, 10], []]]
  inverseQuotients := ![![[], [5], [5], [5], [5], [5], [5], [5], [5]],
    ![[5], [], [5], [5], [5], [5], [5], [5], [5]],
    ![[5], [5], [], [5], [5], [5], [5], [5], [5]],
    ![[5], [5], [5], [], [5], [5], [5], [5], [5]],
    ![[5], [5], [5], [5], [], [5], [5], [5], [5]],
    ![[5], [5], [5], [5], [5], [], [5], [5], [5]],
    ![[5], [5], [5], [5], [5], [5], [], [5], [5]],
    ![[5], [5], [5], [5], [5], [5], [5], [], [5]],
    ![[5], [5], [5], [5], [5], [5], [5], [5], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨false, [0, 0, 0, 0, 1], []⟩,
    ⟨true, [0, 0, 0, 0, 9], [0, 0, 0, 0, 1]⟩,
    ⟨true, [0, 0, 0, 0, 3], [0, 0, 0, 0, 4]⟩,
    ⟨true, [0, 0, 0, 0, 4], [0, 0, 0, 0, 9]⟩,
    ⟨false, [0, 0, 0, 1], [0, 0, 0, 5]⟩,
    ⟨true, [0, 0, 9], [0, 0, 1]⟩,
    ⟨false, [0, 0, 0, 0, 4], []⟩,
    ⟨true, [0, 0, 0, 0, 1], [0, 0, 0, 0, 5]⟩,
    ⟨false, [0, 0, 0, 9], [0, 0, 0, 1]⟩,
    ⟨false, [0, 3], [0, 4]⟩,
    ⟨false, [0, 0, 9], []⟩,
    ⟨true, [3], [4]⟩,
    ⟨true, [0, 9], []⟩,
    ⟨false, [0, 0, 4], []⟩,
    ⟨true, [1], [5]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.aead80e110fd from=translated src=- shape=06f63001 vocab=7af908f0
-/
theorem q3Extension161051_checked : q3Extension161051.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.67663f624aeb from=translated src=- shape=987d0d8b vocab=ad1d2154
-/
theorem q3Extension161051_degree : (poly q3Extension161051.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension161051.modulus).coeff 5 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension161051, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.c9b6b3c21369 from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_161051 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 161051) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 5)
    q3Extension161051_checked q3Extension161051_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
