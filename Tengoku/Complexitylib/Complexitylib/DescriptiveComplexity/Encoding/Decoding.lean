/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Decoding.Defs
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Decoding.Internal

/-!
# Exact decoding of finite structures

Decoding and encoding are inverse on structures, including their relation and
constant interpretations. The decoder succeeds precisely on valid encodings;
every other bit string is rejected. These are computability and correctness
results, without a machine time or space bound.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- The empty input is not a structure encoding. -/
@[simp] theorem decodeStruct_nil (V : Vocabulary) : decodeStruct V [] = none := by
  simp [decodeStruct]

end Complexity.DescriptiveComplexity
