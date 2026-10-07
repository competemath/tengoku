/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.ULift
public import Tengoku.Seed.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `ULift`
-/

public section

universe u v

variable {α} {R : Type v}

namespace ULift

section
variable [Mul R]

/--
@isnad1 id=iff.0h2v.s4.394cd010b91d from=seed src=0 shape=d70b0883 vocab=dbcdca2a
-/
@[to_additive (attr := simp)]
theorem isLeftRegular_up {a : R} : IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular a :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

/--
@isnad1 id=iff.0h2v.s4.7e760cc612d2 from=seed src=0 shape=d70b0883 vocab=daffb7cc
-/
@[to_additive (attr := simp)]
theorem isRightRegular_up {a : R} : IsRightRegular (ULift.up.{u} a) ↔ IsRightRegular a :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

/--
@isnad1 id=iff.0h2v.s4.d38e59254b2c from=seed src=0 shape=d70b0883 vocab=62e25315
-/
@[to_additive (attr := simp)]
theorem isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ IsRegular a := by
  simp [isRegular_iff]

/--
@isnad1 id=iff.0h2v.s4.89b41bf4d164 from=seed src=0 shape=e9f0c92a vocab=d342820e
-/
@[to_additive (attr := simp)]
theorem isLeftRegular_down {a : ULift.{u} R} : IsLeftRegular a.down ↔ IsLeftRegular a :=
  isLeftRegular_up.symm

/--
@isnad1 id=iff.0h2v.s4.d9510c77985f from=seed src=0 shape=e9f0c92a vocab=abaf7501
-/
@[to_additive (attr := simp)]
theorem isRightRegular_down {a : ULift.{u} R} : IsRightRegular a.down ↔ IsRightRegular a :=
  isRightRegular_up.symm

/--
@isnad1 id=iff.0h2v.s4.6ec7d0a79be6 from=seed src=0 shape=e9f0c92a vocab=f14902fe
-/
@[to_additive (attr := simp)]
theorem isRegular_down {a : ULift.{u} R} : IsRegular a.down ↔ IsRegular a :=
  isRegular_up.symm

end

/--
@isnad1 id=iff.0h3v.s4.8a94c2235c03 from=seed src=0 shape=b998e863 vocab=57d8a533
-/
@[simp]
theorem isSMulRegular_iff [SMul α R] {r : α} :
    IsSMulRegular (ULift R) r ↔ IsSMulRegular R r :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

end ULift
