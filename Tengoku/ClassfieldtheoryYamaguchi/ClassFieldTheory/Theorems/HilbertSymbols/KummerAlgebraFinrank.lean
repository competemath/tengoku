/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import Tengoku.Seed.RingTheory.AdjoinRoot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Rank of a Kummer algebra

The rank of `K[X] / (X ^ n - a)` is `n` regardless of whether the polynomial
is irreducible. This is distinct from the index of its norm subgroup.
-/

namespace ClassFieldTheory

universe u

/-- The Kummer algebra has the polynomial's degree as its dimension.
@isnad1 id=eq.0h3v.s9.55ebe54f0c6e from=translated src=- shape=47ec5cca vocab=18430e63
-/
theorem kummerAlgebra_finrank
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    Module.finrank K (KummerAlgebra K n a) = (n : ℕ) := by
  let p : Polynomial K :=
    Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  change Module.finrank K (Polynomial K ⧸ Ideal.span {p}) = (n : ℕ)
  rw [finrank_quotient_span_eq_natDegree]
  exact Polynomial.natDegree_X_pow_sub_C

end ClassFieldTheory
