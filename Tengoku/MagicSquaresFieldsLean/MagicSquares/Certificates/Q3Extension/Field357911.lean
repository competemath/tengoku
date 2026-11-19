import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.ExtensionSquareCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates
open DensePolynomial Polynomial

/--
@isnad1 id=fact.0h0v.s2.f4b96837167a from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
local instance q3Extension357911_prime : Fact (Nat.Prime 71) := ⟨by norm_num⟩

def q3Extension357911 : ExtensionSquareCertificate (ZMod 71) where
  modulus := [1, 1, 0, 1]
  entries := ⟨[69, 4], [13, 55], [63, 12], [66, 8], [1], [7, 63], [10, 59], [60, 16], [4, 67]⟩
  roots := ⟨[59, 43, 5], [0, 10, 10], [25, 44, 8], [63, 51, 32], [1], [54, 27, 21], [23, 8, 28], [21, 15, 34], [38, 43, 25]⟩
  rootQuotients := ⟨[4, 25], [58, 29], [65, 64], [69, 30], [], [69, 15], [22, 3], [26, 20], [20, 57]⟩
  inverses := ![![[], [49, 15, 20], [55, 69, 21], [39, 67, 42], [32, 4, 29], [58, 25, 57], [8, 1, 25], [13, 46, 14], [16, 2, 50]],
    ![[22, 56, 51], [], [36, 40, 6], [42, 23, 7], [63, 70, 46], [55, 69, 21], [39, 67, 42], [67, 35, 23], [13, 46, 14]],
    ![[16, 2, 50], [35, 31, 65], [], [32, 4, 29], [58, 25, 57], [49, 15, 20], [29, 48, 64], [39, 67, 42], [8, 1, 25]],
    ![[32, 4, 29], [29, 48, 64], [39, 67, 42], [], [16, 2, 50], [8, 1, 25], [49, 15, 20], [55, 69, 21], [58, 25, 57]],
    ![[39, 67, 42], [8, 1, 25], [13, 46, 14], [55, 69, 21], [], [16, 2, 50], [58, 25, 57], [63, 70, 46], [32, 4, 29]],
    ![[13, 46, 14], [16, 2, 50], [22, 56, 51], [63, 70, 46], [55, 69, 21], [], [32, 4, 29], [42, 23, 7], [39, 67, 42]],
    ![[63, 70, 46], [32, 4, 29], [42, 23, 7], [22, 56, 51], [13, 46, 14], [39, 67, 42], [], [36, 40, 6], [55, 69, 21]],
    ![[58, 25, 57], [4, 36, 48], [32, 4, 29], [16, 2, 50], [8, 1, 25], [29, 48, 64], [35, 31, 65], [], [49, 15, 20]],
    ![[55, 69, 21], [58, 25, 57], [63, 70, 46], [13, 46, 14], [39, 67, 42], [32, 4, 29], [16, 2, 50], [22, 56, 51], []]]
  inverseQuotients := ![![[], [45], [45], [45], [45], [45], [45], [45], [45]],
    ![[45], [], [45], [45], [45], [45], [45], [45], [45]],
    ![[45], [45], [], [45], [45], [45], [45], [45], [45]],
    ![[45], [45], [45], [], [45], [45], [45], [45], [45]],
    ![[45], [45], [45], [45], [], [45], [45], [45], [45]],
    ![[45], [45], [45], [45], [45], [], [45], [45], [45]],
    ![[45], [45], [45], [45], [45], [45], [], [45], [45]],
    ![[45], [45], [45], [45], [45], [45], [45], [], [45]],
    ![[45], [45], [45], [45], [45], [45], [45], [45], []]]
  powerSteps := [
    ⟨true, [0, 1], []⟩,
    ⟨false, [0, 0, 1], []⟩,
    ⟨true, [1, 1, 70], [70, 0, 1]⟩,
    ⟨false, [3, 3, 69], [69, 1]⟩,
    ⟨true, [7, 28, 26], [64, 59, 4]⟩,
    ⟨true, [25, 38, 35], [46, 36, 37]⟩,
    ⟨true, [19, 43, 3], [52, 33, 18]⟩,
    ⟨false, [32, 18, 37], [45, 9]⟩,
    ⟨true, [26, 2, 13], [45, 54, 20]⟩,
    ⟨true, [57, 42, 25], [14, 52, 27]⟩,
    ⟨false, [13, 4, 13], [41, 57]⟩,
    ⟨false, [65, 44, 43], [33, 27]⟩,
    ⟨false, [15, 16, 68], [21, 3]⟩,
    ⟨false, [37, 70, 15], [46, 9]⟩,
    ⟨true, [37, 16, 15], [34, 41, 12]⟩,
    ⟨false, [37, 53, 5], [54, 12]⟩,
    ⟨true, [41, 28, 30], [30, 33, 25]⟩,
    ⟨true, [70], [1, 47, 48]⟩,
    ⟨true, [0, 1], []⟩]

/--
@isnad1 id=valid.0h0v.s4.68529ece9002 from=translated src=- shape=06f63001 vocab=6213e7a2
-/
theorem q3Extension357911_checked : q3Extension357911.Valid := by
  decide +kernel

/--
@isnad1 id=ne.0h0v.s5.3a02bfc67e55 from=translated src=- shape=987d0d8b vocab=1625d91e
-/
theorem q3Extension357911_degree : (poly q3Extension357911.modulus).degree ≠ 0 := by
  intro h
  have hz : (poly q3Extension357911.modulus).coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
  norm_num [q3Extension357911, poly, DensePolynomial.eval, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_natCast_ite] at hz

/--
@isnad1 id=not.1h1v.s4.54f18262775c from=translated src=- shape=a3262089 vocab=abf65a23
-/
theorem not_squareParker_of_card_357911 {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 357911) : ¬ IsParker F := by
  intro h
  exact h (ExtensionSquareCertificate.exists_magic_of_card (d := 3)
    q3Extension357911_checked q3Extension357911_degree (by decide +kernel) hcard)

end MagicSquares.Certificates
