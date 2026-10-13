/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.EncodingBounds
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.Shape
public import Tengoku

/-!
# Size bounds for Tseitin splitting

The typed transformation is linear in source clauses and literal occurrences.
Because the concrete SAT codec writes variable indices in unary, newly allocated
indices make the honest bit-level bound quadratic in the source encoding length.
-/

public section

namespace Complexity

namespace SAT

namespace CNF

/-- The transformation consumes at most twice as many fresh variables as there
are bits in the source encoding.
@isnad1 id=le.0h1v.s4.69361cc34201 from=translated src=- shape=f9ea0001 vocab=426f6f64
-/
theorem tseitinFreshCount_le_two_mul_encode_length_internal (φ : CNF) :
    φ.tseitinFreshCount ≤ 2 * φ.encode.length := by
  have hfresh := tseitinFreshCount_le_literalCount_add_length_internal φ
  have hlit := literalCount_le_encode_length_internal φ
  have hclauses := length_le_encode_length_internal φ
  omega

/-- The transformed formula has at most three times as many clauses as source
encoding bits, independently of the initial fresh counter.
@isnad1 id=le.0h2v.s4.6e4218d34a3e from=translated src=- shape=224421ba vocab=778327eb
-/
theorem length_to3Aux_le_three_mul_encode_length_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.length ≤ 3 * φ.encode.length := by
  have hout := length_to3Aux_le_internal next φ
  have hlit := literalCount_le_encode_length_internal φ
  have hclauses := length_le_encode_length_internal φ
  exact le_trans hout (by omega)

/-- Every variable emitted from a compact fresh counter is at most three times
the source encoding length.
@isnad1 id=le.4h4v.s6.723febf18d61 from=translated src=- shape=765ed484 vocab=7e2a10be
-/
theorem var_le_three_mul_encode_length_of_mem_to3Aux_internal
    (next : ℕ) (φ : CNF)
    (hsource : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < next)
    (hnext : next ≤ φ.encode.length + 1) {c : Clause}
    (hc : c ∈ (to3Aux next φ).1) {ℓ : Lit} (hℓ : ℓ ∈ c) :
    ℓ.var ≤ 3 * φ.encode.length := by
  have hvar := var_lt_of_mem_to3Aux_internal next φ hsource hc hℓ
  have hfresh := tseitinFreshCount_le_two_mul_encode_length_internal φ
  omega

/-- **Concrete quadratic size bound for a compact fresh counter.** If all
source variables precede `next` and `next ≤ |encode φ| + 1`, then the exact-3
output uses at most `96 * (|encode φ| + 1)^2` bits.
@isnad1 id=le.2h2v.s6.ec7f804c1b68 from=translated src=- shape=09e7499c vocab=71d69685
-/
theorem encode_to3Aux_length_le_internal (next : ℕ) (φ : CNF)
    (hsource : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < next)
    (hnext : next ≤ φ.encode.length + 1) :
    (to3Aux next φ).1.encode.length ≤ 96 * (φ.encode.length + 1) ^ 2 := by
  let n := φ.encode.length
  have h3 := to3Aux_is3CNF_internal next φ
  have hvars : ∀ c ∈ (to3Aux next φ).1, ∀ ℓ ∈ c, ℓ.var ≤ 3 * n := by
    intro c hc ℓ hℓ
    exact var_le_three_mul_encode_length_of_mem_to3Aux_internal
      next φ hsource hnext hc hℓ
  have hencoded := encode_length_le_of_is3CNF_internal h3 hvars
  have hclauses : (to3Aux next φ).1.length ≤ 3 * n := by
    exact length_to3Aux_le_three_mul_encode_length_internal next φ
  calc
    (to3Aux next φ).1.encode.length ≤
        (to3Aux next φ).1.length * (6 * (3 * n) + 14) := hencoded
    _ ≤ (3 * n) * (6 * (3 * n) + 14) :=
      Nat.mul_le_mul_right (6 * (3 * n) + 14) hclauses
    _ ≤ 96 * (n + 1) ^ 2 := by nlinarith

/-- The transformed formula has at most three times as many clauses as source
encoding bits.
@isnad1 id=le.0h1v.s4.76bfbeacfdee from=translated src=- shape=6eeee1bb vocab=23dce9bf
-/
theorem length_to3_le_three_mul_encode_length_internal (φ : CNF) :
    φ.to3.length ≤ 3 * φ.encode.length :=
  length_to3Aux_le_three_mul_encode_length_internal (φ.maxVar + 1) φ

/-- Every transformed variable index is at most three times the source
encoding length.
@isnad1 id=le.2h3v.s5.3f3418cadddb from=translated src=- shape=b3548c57 vocab=332ff9aa
-/
theorem var_le_three_mul_encode_length_of_mem_to3_internal (φ : CNF)
    {c : Clause} (hc : c ∈ φ.to3) {ℓ : Lit} (hℓ : ℓ ∈ c) :
    ℓ.var ≤ 3 * φ.encode.length := by
  apply var_le_three_mul_encode_length_of_mem_to3Aux_internal
    (φ.maxVar + 1) φ
  · intro d hd l hl
    have hld := Clause.var_le_maxVar hl
    have hdφ := CNF.clause_maxVar_le_maxVar hd
    omega
  · have hmax := CNF.maxVar_le_encode_length φ
    omega
  · exact hc
  · exact hℓ

/-- **Concrete quadratic size bound.** Under the current unary-variable SAT
codec, the exact-3 output uses at most `96 * (|encode φ| + 1)^2` bits.
@isnad1 id=le.0h1v.s5.11d0ea8c3728 from=translated src=- shape=a9a0efdd vocab=e6c4b44b
-/
theorem encode_to3_length_le_internal (φ : CNF) :
    φ.to3.encode.length ≤ 96 * (φ.encode.length + 1) ^ 2 := by
  apply encode_to3Aux_length_le_internal (φ.maxVar + 1) φ
  · intro c hc ℓ hℓ
    have hℓc := Clause.var_le_maxVar hℓ
    have hcφ := CNF.clause_maxVar_le_maxVar hc
    omega
  · have hmax := CNF.maxVar_le_encode_length φ
    omega

end CNF

end SAT

end Complexity
