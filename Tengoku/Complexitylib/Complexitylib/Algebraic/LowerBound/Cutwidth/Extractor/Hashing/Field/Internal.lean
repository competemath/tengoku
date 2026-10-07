/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
public import Tengoku

/-!
# Exact collision counting for multiplication followed by projection

For two distinct inputs, multiplication by their difference permutes the
uniform seed. A collision is therefore membership in the projection kernel.
The kernel cardinality identity gives the exact universal bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {F Ω : Type*} [Field F] [AddCommGroup Ω]

theorem fieldHash_add (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection (a + b) seed =
      fieldHash projection a seed + fieldHash projection b seed := by
  simp only [fieldHash, mul_add, map_add]

theorem fieldHash_zero (projection : F →+ Ω) (seed : F) :
    fieldHash projection 0 seed = 0 := by
  simp only [fieldHash, mul_zero, map_zero]

theorem fieldHash_collision_iff (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection a seed = fieldHash projection b seed ↔
      projection (seed * (a - b)) = 0 := by
  simp only [fieldHash, mul_sub, map_sub, sub_eq_zero]

end Algebraic.Cutwidth.Extractor.Internal
