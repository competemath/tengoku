/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QNFMathlib.Data.Int.ModFour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Congruence Criteria Modulo 4

This file develops congruence criteria modulo 4 used in the classification of
rings of integers in quadratic fields. The key distinction is whether `d ≡ 1 (mod 4)`,
which determines whether `𝓞(Q(√d))` is `ℤ[√d]` or `ℤ[(1+√d)/2]`.

## Main Results

### Squarefree Properties
The basic squarefree integer modulo-four facts are imported from
`QNFMathlib.Algebra.Squarefree.Basic`.

### Parity and Squares
The basic parity facts for squares modulo four are imported from
`QNFMathlib.Data.Int.ModFour`.

### Divisibility Criteria
The basic divisibility criteria for `4 ∣ (a'² - d·b'²)` are imported from
`QNFMathlib.Data.Int.ModFour`.

### Branch Utilities
* `exists_k_of_mod_four_eq_one`: Extract `k` from `d % 4 = 1` as `d = 1 + 4k`.
* `mod_four_eq_one_of_exists_k`: Converse of the above.
* `mod_four_branch_split`: Trivial case split `d % 4 = 1 ∨ d % 4 ≠ 1`.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- Extract parameterization `d = 1 + 4k` from `d % 4 = 1`.
@isnad1 id=ex.1h1v.s5.0777543ff03b from=translated src=- shape=cd3daeab vocab=532fda84
-/
theorem exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k := by
  refine ⟨d / 4, ?_⟩
  omega

/-- The converse of `exists_k_of_mod_four_eq_one`.
@isnad1 id=eq.1h1v.s5.632e20d9bab7 from=translated src=- shape=80e3bf9a vocab=532fda84
-/
theorem mod_four_eq_one_of_exists_k {d : ℤ} (h : ∃ k : ℤ, d = 1 + 4 * k) :
    d % 4 = 1 := by
  rcases h with ⟨k, hk⟩
  omega

/-- Canonical branch split by `d % 4 = 1`.
@isnad1 id=or.0h1v.s5.ccab62a9a0d3 from=translated src=- shape=48fc1765 vocab=b6f7664a
-/
theorem mod_four_branch_split (d : ℤ) : d % 4 = 1 ∨ d % 4 ≠ 1 :=
  eq_or_ne (d % 4) 1

end RingOfIntegers
end QuadraticNumberFields
