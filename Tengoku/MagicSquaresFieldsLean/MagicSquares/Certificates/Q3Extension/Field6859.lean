import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.31db4f09118d from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension6859_prime : Fact (Nat.Prime 19) := ⟨by norm_num⟩

def q3Extension6859 : ExtensionSquareCertificate (ZMod 19) where
  modulus := [2, 0, 0, 1]
  entries := ⟨[17, 1], [13, 15], [11, 3], [14, 2], [1], [7, 17], [10, 16], [8, 4], [4, 18]⟩
  roots := ⟨[14, 1, 2], [7, 4, 7], [17, 15, 4], [14, 18, 2], [1], [15, 8, 8], [15, 10, 3], [3, 3, 8], [6, 8, 1]⟩
  rootQuotients := ⟨[4, 4], [18, 11], [6, 16], [15, 4], [], [14, 7], [3, 9], [10, 7], [16, 1]⟩
  inverses := ![![[], [4, 14, 11], [9, 3, 1], [18, 6, 2], [1, 13, 17], [13, 17, 12], [5, 8, 9], [6, 2, 7], [10, 16, 18]],
    ![[15, 5, 8], [], [8, 9, 3], [3, 1, 13], [14, 11, 10], [9, 3, 1], [18, 6, 2], [7, 15, 5], [6, 2, 7]],
    ![[10, 16, 18], [11, 10, 16], [], [1, 13, 17], [13, 17, 12], [4, 14, 11], [16, 18, 6], [18, 6, 2], [5, 8, 9]],
    ![[1, 13, 17], [16, 18, 6], [18, 6, 2], [], [10, 16, 18], [5, 8, 9], [4, 14, 11], [9, 3, 1], [13, 17, 12]],
    ![[18, 6, 2], [5, 8, 9], [6, 2, 7], [9, 3, 1], [], [10, 16, 18], [13, 17, 12], [14, 11, 10], [1, 13, 17]],
    ![[6, 2, 7], [10, 16, 18], [15, 5, 8], [14, 11, 10], [9, 3, 1], [], [1, 13, 17], [3, 1, 13], [18, 6, 2]],
    ![[14, 11, 10], [1, 13, 17], [3, 1, 13], [15, 5, 8], [6, 2, 7], [18, 6, 2], [], [8, 9, 3], [9, 3, 1]],
    ![[13, 17, 12], [12, 4, 14], [1, 13, 17], [10, 16, 18], [5, 8, 9], [16, 18, 6], [11, 10, 16], [], [4, 14, 11]],
    ![[9, 3, 1], [13, 17, 12], [14, 11, 10], [6, 2, 7], [18, 6, 2], [1, 13, 17], [10, 16, 18], [15, 5, 8], []]]
  inverseQuotients := ![![[], [17], [17], [17], [17], [17], [17], [17], [17]],
    ![[17], [], [17], [17], [17], [17], [17], [17], [17]],
    ![[17], [17], [], [17], [17], [17], [17], [17], [17]],
    ![[17], [17], [17], [], [17], [17], [17], [17], [17]],
    ![[17], [17], [17], [17], [], [17], [17], [17], [17]],
    ![[17], [17], [17], [17], [17], [], [17], [17], [17]],
    ![[17], [17], [17], [17], [17], [17], [], [17], [17]],
    ![[17], [17], [17], [17], [17], [17], [17], [], [17]],
    ![[17], [17], [17], [17], [17], [17], [17], [17], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨true, [17], [1]⟩,
    ⟨false, [4], []⟩,
    ⟨true, [0, 16], []⟩,
    ⟨false, [0, 0, 9], []⟩,
    ⟨true, [0, 0, 9], [0, 0, 5]⟩,
    ⟨true, [0, 0, 9], [0, 0, 5]⟩,
    ⟨false, [0, 9], [0, 5]⟩,
    ⟨false, [0, 0, 5], []⟩,
    ⟨true, [0, 0, 7], [0, 0, 6]⟩,
    ⟨false, [0, 16], [0, 11]⟩,
    ⟨true, [1], [9]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.ecb9d256ee44 from=translated src=- shape=06f63001 vocab=6305c533
-/
theorem q3Extension6859_checked : q3Extension6859.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.83ca968afd43 from=translated src=- shape=987d0d8b vocab=c11a4886
-/
theorem q3Extension6859_degree : (poly q3Extension6859.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension6859.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension6859, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.41a6b04b2ae3 from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_6859 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 6859) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension6859_checked q3Extension6859_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
