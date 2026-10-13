/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Oracle.Defs

/-!
# Finite statistical tests as Boolean oracles -- proof internals
-/

public section

namespace Complexity

/--
@isnad1 id=eq.0h2v.s4.f704e4543fd4 from=translated src=- shape=ce30cd2f vocab=541677a2
-/
theorem decodeFixedWidthBoolean?_ofFn_internal
    {length : ℕ} (bits : Fin length → Bool) :
    decodeFixedWidthBoolean? length (List.ofFn bits) = some bits := by
  simp [decodeFixedWidthBoolean?]

/--
@isnad1 id=eq.0h3v.s6.cd9a77bb1009 from=translated src=- shape=87af0703 vocab=0327f566
-/
theorem finiteTestOracle_ofFn_internal
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    (output : Fin outputLength → Bool) :
    finiteTestOracle test (List.ofFn output) = decide (output ∈ test) := by
  simp [finiteTestOracle, decodeFixedWidthBoolean?_ofFn_internal]

/--
@isnad1 id=iff.0h3v.s5.c790d523a0d3 from=translated src=- shape=76ecd115 vocab=60a66a86
-/
theorem finiteTestOracle_ofFn_eq_true_iff_internal
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    (output : Fin outputLength → Bool) :
    finiteTestOracle test (List.ofFn output) = true ↔ output ∈ test := by
  simp [finiteTestOracle_ofFn_internal]

/--
@isnad1 id=eq.1h3v.s4.28a5119aa9a1 from=translated src=- shape=8373d85d vocab=276073b4
-/
theorem finiteTestOracle_eq_false_of_length_ne_internal
    {outputLength : ℕ} (test : Finset (Fin outputLength → Bool))
    {query : List Bool} (hlength : query.length ≠ outputLength) :
    finiteTestOracle test query = false := by
  simp [finiteTestOracle, decodeFixedWidthBoolean?, hlength]

end Complexity
