/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.ThreeSAT
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Defs
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.Correctness
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.Size

/-!
# Size-controlled reduction from CNF-SAT to 3SAT

`CNF.to3` replaces every source clause by an exact-width-three formula. Empty
clauses become a contradictory pair, short clauses repeat literals, and wide
clauses use a chain of fresh variables. The transformation is equisatisfiable
and its concrete unary-variable encoding is quadratically bounded.

`ThreeSAT.reduction` lifts the typed transformation to a total bit-string map.
Malformed source encodings are sent to `ThreeSAT.fallbackEncoding`, a fixed
valid no-instance. Machine-level polynomial-time computability is deliberately
separate from this semantic layer.

## Main results

- `CNF.to3_is3CNF` — the output has exactly three literals per clause
- `CNF.to3_satisfiable_iff` — equisatisfiability
- `CNF.encode_to3_length_le` — quadratic encoded-size bound
- `ThreeSAT.reduction_correct` — total encoded membership equivalence
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace CNF

/-- Splitting from any initial counter produces an exact 3-CNF.
@isnad1 id=is3cnf.0h2v.s3.4b0ec858f1a6 from=translated src=- shape=4c3eae24 vocab=e5f92dff
-/
theorem to3Aux_is3CNF (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.Is3CNF :=
  to3Aux_is3CNF_internal next φ

/-- Splitting from a counter above every source variable preserves and reflects
satisfiability.
@isnad1 id=iff.1h2v.s4.b4aba1a8a608 from=translated src=- shape=d83cab6c vocab=3affb8e6
-/
theorem to3Aux_satisfiable_iff (next : ℕ) (φ : CNF) (hnext : φ.maxVar < next) :
    (to3Aux next φ).1.Satisfiable ↔ φ.Satisfiable := by
  apply satisfiable_to3Aux_iff_internal
  intro c hc ℓ hℓ
  have hℓc := Clause.var_le_maxVar hℓ
  have hcφ := CNF.clause_maxVar_le_maxVar hc
  omega

/-- Splitting produces an exact 3-CNF.
@isnad1 id=is3cnf.0h1v.s2.05202b0973e4 from=translated src=- shape=76a08d12 vocab=dfcc4412
-/
theorem to3_is3CNF (φ : CNF) : φ.to3.Is3CNF :=
  to3_is3CNF_internal φ

/-- Splitting preserves and reflects satisfiability.
@isnad1 id=iff.0h1v.s3.1e0978051082 from=translated src=- shape=6a405104 vocab=c95d9bf1
-/
theorem to3_satisfiable_iff (φ : CNF) :
    φ.to3.Satisfiable ↔ φ.Satisfiable :=
  satisfiable_to3_iff_internal φ

/-- The returned counter is exactly the initial counter plus the number of
fresh variables consumed by the formula.
@isnad1 id=eq.0h2v.s4.b5753c17effa from=translated src=- shape=5229bf6a vocab=65f2fdcc
-/
theorem to3Aux_counter (next : ℕ) (φ : CNF) :
    (to3Aux next φ).2 = next + φ.tseitinFreshCount :=
  to3Aux_counter_internal next φ

/-- The transformed clause count is linear in source literal and clause counts.
@isnad1 id=le.0h1v.s5.16b221ed0d9c from=translated src=- shape=5ec8e204 vocab=18d13e24
-/
theorem length_to3_le (φ : CNF) :
    φ.to3.length ≤ φ.literalCount + 2 * φ.length :=
  length_to3Aux_le_internal (φ.maxVar + 1) φ

/-- Every transformed variable lies below the final fresh counter.
@isnad1 id=lt.2h3v.s5.47e67ea84d62 from=translated src=- shape=0efc18e6 vocab=cc06b976
-/
theorem var_lt_of_mem_to3 (φ : CNF) {c : Clause} (hc : c ∈ φ.to3)
    {ℓ : Lit} (hℓ : ℓ ∈ c) :
    ℓ.var < φ.maxVar + 1 + φ.tseitinFreshCount :=
  var_lt_of_mem_to3_internal φ hc hℓ

/-- The concrete unary-variable encoding of the output is quadratically
bounded in the source encoding length.
@isnad1 id=le.0h1v.s5.11d0ea8c3728 from=translated src=- shape=a9a0efdd vocab=e6c4b44b
-/
theorem encode_to3_length_le (φ : CNF) :
    φ.to3.encode.length ≤ 96 * (φ.encode.length + 1) ^ 2 :=
  encode_to3_length_le_internal φ

/-- A compact fresh start preserves the same quadratic encoded-size bound as
the canonical transformation.
@isnad1 id=le.2h2v.s6.6b9418256521 from=translated src=- shape=c874847d vocab=9f85e725
-/
theorem encode_to3Aux_length_le (next : ℕ) (φ : CNF)
    (hfresh : φ.maxVar < next) (hnext : next ≤ φ.encode.length + 1) :
    (to3Aux next φ).1.encode.length ≤ 96 * (φ.encode.length + 1) ^ 2 := by
  apply encode_to3Aux_length_le_internal
  · intro c hc ℓ hℓ
    have hℓc := Clause.var_le_maxVar hℓ
    have hcφ := CNF.clause_maxVar_le_maxVar hc
    omega
  · exact hnext

end CNF

namespace ThreeSAT

/-- Total bit-string reduction from encoded CNF-SAT to encoded 3SAT. Malformed
inputs map to a fixed valid no-instance. -/
def reduction (z : List Bool) : List Bool :=
  match CNF.decode? z with
  | some φ => (CNF.to3Aux (z.length + 1) φ).1.encode
  | none => fallbackEncoding

/-- A typed CNF's transformed encoding belongs to 3SAT exactly when the source
formula is satisfiable.
@isnad1 id=iff.0h1v.s4.b696ad958db2 from=translated src=- shape=cbcb1740 vocab=8c391819
-/
theorem encode_to3_mem_language_iff (φ : CNF) :
    φ.to3.encode ∈ language ↔ φ.Satisfiable := by
  rw [encode_mem_language_iff]
  constructor
  · exact fun h => (CNF.to3_satisfiable_iff φ).mp h.2
  · exact fun h => ⟨CNF.to3_is3CNF φ, (CNF.to3_satisfiable_iff φ).mpr h⟩

/-- A typed CNF split from any fresh counter belongs to 3SAT exactly when the
source formula is satisfiable.
@isnad1 id=iff.1h2v.s4.aef838e254e5 from=translated src=- shape=08b19c87 vocab=91536b1c
-/
theorem encode_to3Aux_mem_language_iff (next : ℕ) (φ : CNF)
    (hnext : φ.maxVar < next) :
    (CNF.to3Aux next φ).1.encode ∈ language ↔ φ.Satisfiable := by
  rw [encode_mem_language_iff]
  constructor
  · exact fun h => (CNF.to3Aux_satisfiable_iff next φ hnext).mp h.2
  · exact fun h => ⟨CNF.to3Aux_is3CNF next φ,
      (CNF.to3Aux_satisfiable_iff next φ hnext).mpr h⟩

/-- **Semantic correctness of the total encoded reduction.**
@isnad1 id=iff.0h1v.s4.8dbe0fbcb142 from=translated src=- shape=459856d8 vocab=cac41111
-/
theorem reduction_correct (z : List Bool) :
    reduction z ∈ language ↔ z ∈ CNFSAT.language := by
  cases hdecode : CNF.decode? z with
  | none =>
      have hnotSource : z ∉ CNFSAT.language := by
        rw [CNFSAT.mem_language_iff_decode]
        rintro ⟨φ, hφ, _⟩
        rw [hdecode] at hφ
        contradiction
      simp [reduction, hdecode, fallbackEncoding_not_mem_language, hnotSource]
  | some φ =>
      have hz : z = φ.encode := CNF.decode?_sound hdecode
      rw [hz]
      have hfresh : φ.maxVar < φ.encode.length + 1 := by
        have hmax := CNF.maxVar_le_encode_length φ
        omega
      rw [show reduction φ.encode =
          (CNF.to3Aux (φ.encode.length + 1) φ).1.encode by simp [reduction],
        encode_to3Aux_mem_language_iff _ _ hfresh,
        CNFSAT.encode_mem_language_iff]

/-- Source-first orientation of `reduction_correct`, matching the convention
used by polynomial-time many-one reductions.
@isnad1 id=iff.0h1v.s4.f68eaefb3742 from=translated src=- shape=3e739b6e vocab=cac41111
-/
theorem mem_language_iff_reduction_mem (z : List Bool) :
    z ∈ CNFSAT.language ↔ reduction z ∈ language :=
  (reduction_correct z).symm

/-- The total encoded reduction has a quadratic output-length bound, including
its fixed fallback value on malformed inputs.
@isnad1 id=le.0h1v.s5.be1acaa68705 from=translated src=- shape=63d13c47 vocab=b6733b4f
-/
theorem reduction_length_le (z : List Bool) :
    (reduction z).length ≤ 96 * (z.length + 1) ^ 2 := by
  cases hdecode : CNF.decode? z with
  | none =>
      rw [show reduction z = fallbackEncoding by simp [reduction, hdecode]]
      have hfallback : fallbackEncoding.length = 28 := by decide
      rw [hfallback]
      have hsucc : 1 ≤ z.length + 1 := by omega
      have hpow : 1 ≤ (z.length + 1) ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul hsucc hsucc
      calc
        28 ≤ 96 := by omega
        _ = 96 * 1 := by omega
        _ ≤ 96 * (z.length + 1) ^ 2 := Nat.mul_le_mul_left 96 hpow
  | some φ =>
      have hz : z = φ.encode := CNF.decode?_sound hdecode
      subst z
      have hfresh : φ.maxVar < φ.encode.length + 1 := by
        have hmax := CNF.maxVar_le_encode_length φ
        omega
      simpa [reduction] using CNF.encode_to3Aux_length_le
        (φ.encode.length + 1) φ hfresh le_rfl

end ThreeSAT

end SAT

end Complexity
