/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Internal

/-!
# Universal linear hashing from a finite field

Field multiplication followed by any surjective additive projection is a
universal family, with exact collision fraction reciprocal to the output
cardinality. Every fixed-seed map is additive and sends zero to zero. This
does not assert pairwise independence: all maps agree at the zero input.
The multiply-and-truncate source is credited in `Hashing.Field.Defs`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

variable {F Ω : Type*} [Field F] [AddCommGroup Ω]

/-- Every fixed-seed field hash preserves source addition.
@isnad1 id=eq.0h6v.s6.513784da37d9 from=translated src=- shape=35c87b9e vocab=9e213ef6
-/
theorem fieldHash_add (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection (a + b) seed =
      fieldHash projection a seed + fieldHash projection b seed :=
  Internal.fieldHash_add projection a b seed

/-- Every fixed-seed field hash sends zero to zero.
@isnad1 id=eq.0h4v.s6.eeb33498ea7c from=translated src=- shape=68e3518e vocab=2b5e930a
-/
theorem fieldHash_zero (projection : F →+ Ω) (seed : F) :
    fieldHash projection 0 seed = 0 :=
  Internal.fieldHash_zero projection seed

/-- Colliding hashes are exactly the seeds whose scaled difference lies in the kernel.
@isnad1 id=iff.0h6v.s7.812bc0ecc830 from=translated src=- shape=1fbd106b vocab=5a2d5571
-/
theorem fieldHash_collision_iff (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection a seed = fieldHash projection b seed ↔
      projection (seed * (a - b)) = 0 :=
  Internal.fieldHash_collision_iff projection a b seed

end Algebraic.Cutwidth.Extractor
