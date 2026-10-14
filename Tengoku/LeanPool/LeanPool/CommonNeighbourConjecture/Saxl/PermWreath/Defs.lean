/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import Tengoku

/-!
# Permutation wreath products

This file defines the wreath product attached to an arbitrary action of a top
group on an index type.  The top group acts on the base group by contravariant
reindexing, so that

`(reindexAut X Q ι q f) i = f (q⁻¹ • i)`.

Unlike `RegularWreathProduct`, the action of `Q` on `ι` need not be regular.
-/

@[expose] public section

namespace Saxl

variable (X Q ι : Type*) [Group X] [Group Q] [MulAction Q ι]

/-- The action of `Q` on the base group `ι → X` by contravariant
reindexing. -/
def reindexAut : Q →* MulAut (ι → X) where
  toFun q := MulEquiv.arrowCongr (MulAction.toPerm q) (MulEquiv.refl X)
  map_one' := by
    ext f i
    simp
  map_mul' q r := by
    ext f i
    simp [mul_smul]

/--
@isnad1 id=eq.0h6v.s9.6a6f11ff5416 from=translated src=- shape=fd8a315c vocab=a55db42c
-/
@[simp]
theorem reindexAut_apply (q : Q) (f : ι → X) (i : ι) :
    reindexAut X Q ι q f i = f (q⁻¹ • i) := rfl

/-- The permutation wreath product `X wr_ι Q`, with base group `ι → X`
and the specified action of `Q` on `ι`. -/
abbrev PermWreath := (ι → X) ⋊[reindexAut X Q ι] Q

namespace PermWreath

/-- The canonical inclusion of the base group into the permutation wreath
product. -/
def base : (ι → X) →* PermWreath X Q ι :=
  SemidirectProduct.inl

/-- The canonical inclusion of the top group into the permutation wreath
product. -/
def top : Q →* PermWreath X Q ι :=
  SemidirectProduct.inr

/--
@isnad1 id=eq.0h4v.s7.96a863226dee from=translated src=- shape=066fb497 vocab=0f0e1a04
-/
@[simp]
theorem base_left (f : ι → X) : (base X Q ι f).left = f := rfl

/--
@isnad1 id=eq.0h4v.s7.b43943f23f8b from=translated src=- shape=11b76dc1 vocab=a8261ffc
-/
@[simp]
theorem base_right (f : ι → X) : (base X Q ι f).right = 1 := rfl

/--
@isnad1 id=eq.0h4v.s7.7308979575ba from=translated src=- shape=31905931 vocab=ccb1338b
-/
@[simp]
theorem top_left (q : Q) : (top X Q ι q).left = 1 := rfl

/--
@isnad1 id=eq.0h4v.s7.2dc113d405fe from=translated src=- shape=67411dde vocab=48f5ab6c
-/
@[simp]
theorem top_right (q : Q) : (top X Q ι q).right = q := rfl

/-- Extensionality in the base and top coordinates.
@isnad1 id=eq.2h5v.s7.d2a16f01f10d from=translated src=- shape=90989172 vocab=7f830cf6
-/
theorem ext {g h : PermWreath X Q ι} (hbase : g.left = h.left)
    (htop : g.right = h.right) : g = h :=
  SemidirectProduct.ext hbase htop

end PermWreath

end Saxl
