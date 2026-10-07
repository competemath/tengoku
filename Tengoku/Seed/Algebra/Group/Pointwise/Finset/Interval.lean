/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Group.Pointwise.Interval
public import Tengoku.Seed.Order.Interval.Finset.Defs
public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Basic

/-! # Pointwise operations on intervals

This should be kept in sync with `Mathlib/Algebra/Order/Group/Pointwise/Interval.lean`.
-/

public section

variable {α : Type*}

namespace Finset

open scoped Pointwise

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Finset.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α] [DecidableEq α]
variable [MulLeftMono α] [MulRightMono α]

/--
@isnad1 id=le.0h5v.s6.82de6699b1f1 from=seed src=0 shape=fe58d594 vocab=68dc2331
-/
@[to_additive Icc_add_Icc_subset]
theorem Icc_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Icc c d ⊆ Icc (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

/--
@isnad1 id=le.0h3v.s6.eb2654d729c6 from=seed src=0 shape=1ac7d027 vocab=70384342
-/
@[to_additive Iic_add_Iic_subset]
theorem Iic_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b ⊆ Iic (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iic_subset' _ _

/--
@isnad1 id=le.0h3v.s6.eb99f667aed0 from=seed src=0 shape=1ac7d027 vocab=f6e33af3
-/
@[to_additive Ici_add_Ici_subset]
theorem Ici_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b ⊆ Ici (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ici_subset' _ _

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α] [DecidableEq α]
variable [MulLeftStrictMono α] [MulRightStrictMono α]

/--
@isnad1 id=le.0h5v.s6.ccaea3c77e95 from=seed src=0 shape=3cba94a3 vocab=d2d0af19
-/
@[to_additive Icc_add_Ico_subset]
theorem Icc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Ico c d ⊆ Ico (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

/--
@isnad1 id=le.0h5v.s6.cc5204555ea4 from=seed src=0 shape=fe58d594 vocab=d2d0af19
-/
@[to_additive Ico_add_Icc_subset]
theorem Ico_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Icc c d ⊆ Ico (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Icc_subset' _ _ _ _

/--
@isnad1 id=le.0h5v.s6.ceabc0e25fd8 from=seed src=0 shape=3cba94a3 vocab=cd114665
-/
@[to_additive Ioc_add_Ico_subset]
theorem Ioc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ioc a b * Ico c d ⊆ Ioo (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ioc_mul_Ico_subset' _ _ _ _

/--
@isnad1 id=le.0h5v.s6.764a19666e84 from=seed src=0 shape=3cba94a3 vocab=cd114665
-/
@[to_additive Ico_add_Ioc_subset]
theorem Ico_mul_Ioc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

/--
@isnad1 id=le.0h3v.s6.cb569dc1dbc5 from=seed src=0 shape=dba56cdc vocab=f053a7ff
-/
@[to_additive Iic_add_Iio_subset]
theorem Iic_mul_Iio_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iio b ⊆ Iio (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iio_subset' _ _

/--
@isnad1 id=le.0h3v.s6.a00de3f931fd from=seed src=0 shape=1ac7d027 vocab=f053a7ff
-/
@[to_additive Iio_add_Iic_subset]
theorem Iio_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b ⊆ Iio (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iio_mul_Iic_subset' _ _

/--
@isnad1 id=le.0h3v.s6.e75806ba3b09 from=seed src=0 shape=1ac7d027 vocab=d4982466
-/
@[to_additive Ioi_add_Ici_subset]
theorem Ioi_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ioi_mul_Ici_subset' _ _

/--
@isnad1 id=le.0h3v.s6.dfdf0b71f924 from=seed src=0 shape=dba56cdc vocab=d4982466
-/
@[to_additive Ici_add_Ioi_subset]
theorem Ici_mul_Ioi_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ioi_subset' _ _

end ContravariantLT

end Finset
