/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# Characteristic two monoids

We say that a monoid `M` has *characteristic two* if `x + x = 0` for any `x : M`.
Such monoids are secretly abelian groups, and subtraction is the same as addition.
-/

@[expose] public section

namespace IMOSL
namespace Extra

@[deprecated "Too greedy: import `Mathlib.Algebra.CharP.Two` instead." (since := "2025-03-08")]
class CharTwo (M) [AddMonoid M] : Prop where
  add_self_eq_zero : ∀ x : M, x + x = 0

namespace CharTwo

section

variable [AddMonoid M] [CharTwo M]

/--
@isnad1 id=eq.0h3v.s5.fe968a0866c5 from=translated src=- shape=18384a85 vocab=b5b1f869
-/
theorem add_add_cancel_left (x y : M) : x + (x + y) = y := by
  rw [← add_assoc, add_self_eq_zero, zero_add]

/--
@isnad1 id=eq.0h3v.s5.7c1eeb20b79c from=translated src=- shape=f19624ad vocab=b5b1f869
-/
theorem add_add_cancel_right (x y : M) : x + y + y = x := by
  rw [add_assoc, add_self_eq_zero, add_zero]

/--
@isnad1 id=eq.0h4v.s6.e6db2bb77291 from=translated src=- shape=ae616be3 vocab=b5b1f869
-/
theorem add_add_add_cancel_middle (x y z : M) : (x + y) + (y + z) = x + z := by
  rw [← add_assoc, add_add_cancel_right]

/--
@isnad1 id=eq.0h3v.s5.769f0e920a0b from=translated src=- shape=64e739e2 vocab=b5b1f869
-/
theorem add_comm (x y : M) : x + y = y + x := by
  rw [← add_add_cancel_right (x + y) (y + x),
    add_add_add_cancel_middle, add_self_eq_zero, zero_add]

/--
@isnad1 id=eq.0h3v.s5.f8e0d16c9e17 from=translated src=- shape=52f1fde4 vocab=b5b1f869
-/
theorem add_add_cancel_middle₁ (x y : M) : x + (y + x) = y := by
  rw [add_comm, add_add_cancel_right]

/--
@isnad1 id=eq.0h3v.s5.4070122d12eb from=translated src=- shape=4a6c7d73 vocab=b5b1f869
-/
theorem add_add_cancel_middle₂ (x y : M) : x + y + x = y := by
  rw [add_comm, add_add_cancel_left]

/--
@isnad1 id=iff.0h4v.s5.7d0aa2a8719f from=translated src=- shape=d2989387 vocab=b5b1f869
-/
theorem add_right_inj {x y z : M} : x + y = x + z ↔ y = z :=
  ⟨λ h ↦ by rw [← add_add_cancel_left x y, h, add_add_cancel_left], congr_arg₂ _ rfl⟩

/--
@isnad1 id=iff.0h4v.s5.8988143f4a73 from=translated src=- shape=ecd2a00b vocab=b5b1f869
-/
theorem add_left_inj {x y z : M} : x + z = y + z ↔ x = y := by
  rw [add_comm, add_comm y, add_right_inj]

/--
@isnad1 id=iff.0h4v.s5.0fb647a9b3ff from=translated src=- shape=e6076a00 vocab=b5b1f869
-/
theorem add_eq_iff_eq_add {x y z : M} : x + y = z ↔ x = z + y := by
  rw [← add_left_inj (z := y), add_add_cancel_right]

/--
@isnad1 id=iff.0h4v.s5.f79bc6351906 from=translated src=- shape=463a5cfc vocab=b5b1f869
-/
theorem add_eq_iff_eq_add' {x y z : M} : x + y = z ↔ x = y + z := by
  rw [add_eq_iff_eq_add, add_comm]

/--
@isnad1 id=iff.0h4v.s5.cf9f1a98170b from=translated src=- shape=d9aec62e vocab=b5b1f869
-/
theorem add_eq_iff_eq_add'' {x y z : M} : x + y = z ↔ y = x + z := by
  rw [add_comm, add_eq_iff_eq_add']

/--
@isnad1 id=iff.0h4v.s5.a94bbfa380db from=translated src=- shape=9ee080a7 vocab=b5b1f869
-/
theorem add_eq_iff_eq_add''' {x y z : M} : x + y = z ↔ y = z + x := by
  rw [add_eq_iff_eq_add'', add_comm]

/--
@isnad1 id=iff.0h3v.s5.507612e00071 from=translated src=- shape=7b927035 vocab=b5b1f869
-/
theorem add_eq_zero_iff_eq {x y : M} : x + y = 0 ↔ x = y := by
  rw [add_eq_iff_eq_add, zero_add]

/--
@isnad1 id=eq.0h4v.s6.9eaa422f6d7b from=translated src=- shape=25bd63ff vocab=b5b1f869
-/
theorem add_add_add_cancel_left (x y z : M) : (x + y) + (x + z) = y + z := by
  rw [← add_assoc, add_add_cancel_middle₂]

/--
@isnad1 id=eq.0h4v.s6.3c681f20b552 from=translated src=- shape=9a6fed62 vocab=b5b1f869
-/
theorem add_add_add_cancel_right (x y z : M) : (x + z) + (y + z) = x + y := by
  rw [add_assoc, add_add_cancel_middle₁]

end

/-! ### `CharTwo` on groups -/

section

variable [AddGroup G] [CharTwo G]

/--
@isnad1 id=eq.0h2v.s4.004f943b70d8 from=translated src=- shape=fb05e317 vocab=c44eb5dd
-/
theorem neg_eq_self (x : G) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero x)

/--
@isnad1 id=eq.0h1v.s5.1a1212afe48c from=translated src=- shape=2f12b6fc vocab=76e18ad7
-/
theorem neg_eq_self' : (λ x : G ↦ -x) = id :=
  funext neg_eq_self

/--
@isnad1 id=eq.0h3v.s5.2dfdda6bb159 from=translated src=- shape=e43ee71b vocab=05bc709e
-/
theorem sub_eq_add (x y : G) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self]

/--
@isnad1 id=eq.0h1v.s5.e3fa44806e2c from=translated src=- shape=e4d9bced vocab=05bc709e
-/
theorem sub_eq_add' : (λ x y : G ↦ x - y) = (· + ·) :=
  funext₂ sub_eq_add

end
