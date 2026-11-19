import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.1e8f35d99f49 from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension12167_prime : Fact (Nat.Prime 23) := ⟨by norm_num⟩

def q3Extension12167 : ExtensionSquareCertificate (ZMod 23) where
  modulus := [3, 1, 0, 1]
  entries := ⟨[14, 10, 1], [18, 6, 19], [17, 7, 3], [4, 20, 2], [1], [21, 3, 21], [8, 16, 20], [7, 17, 4], [11, 13, 22]⟩
  roots := ⟨[9, 5, 3], [9, 19, 6], [7, 18, 2], [2, 5], [1], [2, 8, 3], [22, 2, 9], [7, 5, 6], [12, 12, 6]⟩
  rootQuotients := ⟨[7, 9], [21, 13], [3, 4], [], [], [2, 9], [13, 12], [14, 13], [6, 13]⟩
  inverses := ![![[], [11, 7, 22], [7, 17, 14], [14, 11, 5], [9, 12, 18], [3, 4, 6], [8, 3, 16], [20, 19, 17], [16, 6, 9]],
    ![[12, 16, 1], [], [2, 18, 4], [10, 21, 20], [15, 20, 7], [7, 17, 14], [14, 11, 5], [19, 10, 15], [20, 19, 17]],
    ![[16, 6, 9], [21, 5, 19], [], [9, 12, 18], [3, 4, 6], [11, 7, 22], [13, 2, 3], [14, 11, 5], [8, 3, 16]],
    ![[9, 12, 18], [13, 2, 3], [14, 11, 5], [], [16, 6, 9], [8, 3, 16], [11, 7, 22], [7, 17, 14], [3, 4, 6]],
    ![[14, 11, 5], [8, 3, 16], [20, 19, 17], [7, 17, 14], [], [16, 6, 9], [3, 4, 6], [15, 20, 7], [9, 12, 18]],
    ![[20, 19, 17], [16, 6, 9], [12, 16, 1], [15, 20, 7], [7, 17, 14], [], [9, 12, 18], [10, 21, 20], [14, 11, 5]],
    ![[15, 20, 7], [9, 12, 18], [10, 21, 20], [12, 16, 1], [20, 19, 17], [14, 11, 5], [], [2, 18, 4], [7, 17, 14]],
    ![[3, 4, 6], [4, 13, 8], [9, 12, 18], [16, 6, 9], [8, 3, 16], [13, 2, 3], [21, 5, 19], [], [11, 7, 22]],
    ![[7, 17, 14], [3, 4, 6], [15, 20, 7], [20, 19, 17], [14, 11, 5], [9, 12, 18], [16, 6, 9], [12, 16, 1], []]]
  inverseQuotients := ![![[], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18]],
    ![[8, 18], [], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18]],
    ![[8, 18], [8, 18], [], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18]],
    ![[8, 18], [8, 18], [8, 18], [], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18]],
    ![[8, 18], [8, 18], [8, 18], [8, 18], [], [8, 18], [8, 18], [8, 18], [8, 18]],
    ![[8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [], [8, 18], [8, 18], [8, 18]],
    ![[8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [], [8, 18], [8, 18]],
    ![[8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [], [8, 18]],
    ![[8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], [8, 18], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨true, [3, 1, 20], [22, 0, 1]⟩,
    ⟨true, [9, 7, 8], [20, 17, 9]⟩,
    ⟨true, [4, 7, 6], [14, 20, 18]⟩,
    ⟨true, [1, 2, 2], [15, 15, 13]⟩,
    ⟨true, [11, 19, 7], [4, 8, 4]⟩,
    ⟨false, [13, 5, 6], [13, 3]⟩,
    ⟨false, [12, 8, 7], [14, 13]⟩,
    ⟨false, [15, 2, 22], [20, 3]⟩,
    ⟨false, [7, 15, 19], [19, 1]⟩,
    ⟨true, [1, 3, 6], [15, 18, 16]⟩,
    ⟨true, [22], [8, 13, 13]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.7be643e55c64 from=translated src=- shape=06f63001 vocab=3d7c0f61
-/
theorem q3Extension12167_checked : q3Extension12167.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.c7a37c65ef62 from=translated src=- shape=987d0d8b vocab=676f833d
-/
theorem q3Extension12167_degree : (poly q3Extension12167.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension12167.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension12167, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.fd15d0180b61 from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_12167 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 12167) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension12167_checked q3Extension12167_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
