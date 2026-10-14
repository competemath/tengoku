/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Extra.CharTwo.Defs
public import Tengoku

/-!
# Characteristic two (semi)rings

We prove several lemmas about `CharTwo` semirings.
The lemmas here do not need extra imports beyond `Mathlib.Algebra.Ring.Defs`.
-/

@[expose] public section

namespace IMOSL
namespace Extra
namespace CharTwo

/--
@isnad1 id=chartwo.1h1v.s5.4757b704b916 from=translated src=- shape=9defbe27 vocab=1fcfc7c6
-/
theorem Semiring_of_two_eq_zero [NonAssocSemiring R] (h : (2 : R) = 0) : CharTwo R :=
  ⟨λ x ↦ by rw [← two_mul, h, zero_mul]⟩

section

variable [NonAssocSemiring R] [CharTwo R]

/--
@isnad1 id=eq.0h1v.s5.3eaa11c524b4 from=translated src=- shape=5e3b0e7f vocab=1fcfc7c6
-/
theorem two_eq_zero : (2 : R) = 0 := by
  rw [← one_add_one_eq_two, add_self_eq_zero]

/--
@isnad1 id=eq.1h3v.s7.4397e8a000ea from=translated src=- shape=caff3970 vocab=846fd70f
-/
lemma add_mul_self_of_Commute {x y : R} (h : x * y = y * x) :
    (x + y) * (x + y) = x * x + y * y := by
  rw [add_mul, mul_add, mul_add, ← add_assoc, h, add_add_cancel_right]

/--
@isnad1 id=eq.0h2v.s6.576eb2741e82 from=translated src=- shape=840f3f26 vocab=846fd70f
-/
lemma add_one_mul_self (x : R) : (x + 1) * (x + 1) = x * x + 1 := by
  rw [add_mul_self_of_Commute ((mul_one x).trans (one_mul x).symm), one_mul]

/--
@isnad1 id=iff.0h2v.s6.86bcad2c3726 from=translated src=- shape=776ca152 vocab=f9d4d1b3
-/
lemma mul_self_eq_one_iff [NoZeroDivisors R] {x : R} : x * x = 1 ↔ x = 1 := by
  rw [← add_eq_zero_iff_eq, ← add_one_mul_self, mul_self_eq_zero, add_eq_zero_iff_eq]

end

/-! ### Associative semiring -/

section

variable [Semiring R] [CharTwo R]

/--
@isnad1 id=eq.1h3v.s7.7b3a4d837ae1 from=translated src=- shape=24bf3e19 vocab=147a186a
-/
lemma add_sq_of_Commute {x y : R} (h : x * y = y * x) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  rw [sq, sq, sq, add_mul_self_of_Commute h]

/--
@isnad1 id=eq.0h2v.s6.289496dfcdea from=translated src=- shape=6d1b3d4c vocab=dba732e8
-/
lemma add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 := by
  rw [sq, sq, add_one_mul_self]

/--
@isnad1 id=iff.0h2v.s6.1a7950ac9cfd from=translated src=- shape=e935eb00 vocab=72edd39f
-/
lemma sq_eq_one_iff [NoZeroDivisors R] {x : R} : x ^ 2 = 1 ↔ x = 1 := by
  rw [sq, mul_self_eq_one_iff]

end

/-! ### Commutative semiring -/

section

variable [CommSemiring R] [CharTwo R]

/--
@isnad1 id=eq.0h3v.s6.546490216f12 from=translated src=- shape=f9a8cdef vocab=ba36f9ab
-/
lemma add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y :=
  add_mul_self_of_Commute (mul_comm x y)

/--
@isnad1 id=eq.0h3v.s6.68a50ec87533 from=translated src=- shape=a29a719e vocab=bdb696d9
-/
lemma add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_sq_of_Commute (mul_comm x y)

/--
@isnad1 id=iff.0h3v.s6.f51f1451e522 from=translated src=- shape=a8ad5108 vocab=faff63a5
-/
lemma mul_self_eq_iff [NoZeroDivisors R] {x y : R} : x * x = y * y ↔ x = y := by
  rw [← add_eq_zero_iff_eq, ← add_mul_self, mul_self_eq_zero, add_eq_zero_iff_eq]

/--
@isnad1 id=iff.0h3v.s6.8aebaf2507cf from=translated src=- shape=73f8731c vocab=45233789
-/
lemma sq_eq_iff [NoZeroDivisors R] {x y : R} : x ^ 2 = y ^ 2 ↔ x = y := by
  rw [sq, sq, mul_self_eq_iff]

end
