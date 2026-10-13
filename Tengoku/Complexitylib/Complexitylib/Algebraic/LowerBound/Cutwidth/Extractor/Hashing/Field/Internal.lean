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

/--
@isnad1 id=eq.0h6v.s6.513784da37d9 from=translated src=- shape=35c87b9e vocab=9e213ef6
-/
theorem fieldHash_add (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection (a + b) seed =
      fieldHash projection a seed + fieldHash projection b seed := by
  simp only [fieldHash, mul_add, map_add]

/--
@isnad1 id=eq.0h4v.s6.eeb33498ea7c from=translated src=- shape=68e3518e vocab=2b5e930a
-/
theorem fieldHash_zero (projection : F →+ Ω) (seed : F) :
    fieldHash projection 0 seed = 0 := by
  simp only [fieldHash, mul_zero, map_zero]

/--
@isnad1 id=iff.0h6v.s7.812bc0ecc830 from=translated src=- shape=1fbd106b vocab=5a2d5571
-/
theorem fieldHash_collision_iff (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection a seed = fieldHash projection b seed ↔
      projection (seed * (a - b)) = 0 := by
  simp only [fieldHash, mul_sub, map_sub, sub_eq_zero]

end Algebraic.Cutwidth.Extractor.Internal
