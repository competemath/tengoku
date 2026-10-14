/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5Answers.SqSubOneMap
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5Answers.F3Map2
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5Answers.Z4Map
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5General.A5CommLift
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5General.A5QuasiPeriodic
public import Tengoku.Imoshortlist.IMOSLLean4.Extra.SquareLike

/-!
# IMO 2012 A5 (Case 2: `f(-1) = 0`, `char(R) ∤ 2`)

We solve the case where `f` is reduced good, `f(-1) = 0`, and `char(R) ∤ 2`.
Actually, `f(-1) = 0` implies that `f` is even, so the latter is assumed instead.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization
namespace Case2

/-! ### General lemmas -/

section

variable [NonAssocRing R] [NonAssocSemiring S] {f : R → S}

/--
@isnad1 id=eq.2h4v.s6.e85ef3e4a4c6 from=translated src=- shape=a2577eb3 vocab=71898d8c
-/
theorem map_even_of_map_one (hf : good f) (h : f (-1) = 0) (x) : f (-x) = f x := by
  specialize hf (x + 1) (-1)
  rwa [h, mul_zero, zero_add, add_neg_cancel_right,
    mul_neg_one, neg_add, neg_add_cancel_right] at hf

variable (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x)
include hf h

/-- (2.1)
@isnad1 id=eq.2h5v.s7.082f020e3c8b from=translated src=- shape=9a3f3ea9 vocab=eef1f8a0
-/
theorem Eq1 (x y) : f (x * y - 1) = f x * f y + f (x - y) := by
  rw [← h y, sub_eq_add_neg x, ← hf.is_good, mul_neg, neg_add_eq_sub, ← neg_sub, h]

omit h in
/-- (2.2)
@isnad1 id=eq.1h4v.s7.4cef36474d7b from=translated src=- shape=e245ef91 vocab=205c09d3
-/
theorem Eq2 (x) : f (x * 2 - 1) = f (x - 1) * f 2 + f (x + 1) := by
  have h0 := hf.is_good (x - 1) (1 + 1)
  rwa [sub_add_add_cancel, one_add_one_eq_two, mul_two, add_assoc,
    sub_add_cancel, ← add_sub_right_comm, ← mul_two] at h0

/-- (2.3)
@isnad1 id=eq.2h4v.s7.9cc8af7da995 from=translated src=- shape=498567b3 vocab=74d92b87
-/
theorem Eq3 (x) : f (x * 2 + 1) = f (x + 1) * f 2 + f (x - 1) := by
  have h0 := Eq2 hf (-x)
  rwa [neg_mul, ← neg_add', h, ← neg_add', h, neg_add_eq_sub, ← neg_sub, h] at h0

/-- (2.5)
@isnad1 id=eq.4h5v.s7.b43c59afa894 from=translated src=- shape=6bbaadf9 vocab=3fecf9ef
-/
theorem Eq5 {x} (h0 : f x = 0) (h1 : f (x + 1) = 0) : ∀ y, f (y + (2 * x + 1)) = f y :=
  suffices ∀ y, f (x + y + 1) = f (x - y) from λ y ↦ by
    rw [two_mul, ← add_assoc, add_left_comm, this, sub_add_cancel_right, h]
  λ y ↦ by
    have h2 : f (x * ((x + 1) * y) + 1) = f ((x + 1) * (x * y) + 1) := by
      rw [add_one_mul x, mul_add, add_one_mul x]
    have h3 : x + (x + 1) * y = (x + 1) * (y + 1) - 1 := by
      rw [mul_add_one _ y, add_sub_assoc, add_sub_cancel_right, add_comm]
    rwa [hf.is_good, h3, Eq1 hf h, hf.is_good, ← add_rotate, ← mul_add_one x,
      hf.is_good, h0, h1, zero_mul, zero_add, zero_mul, zero_add, zero_add,
      zero_mul, zero_add, add_sub_add_right_eq_sub, ← add_assoc, eq_comm] at h2

end

namespace CommCase

variable [Ring R] [CommRing S] [NoZeroDivisors S] {f : R → S}
  (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x)
include hf h

omit [NoZeroDivisors S] in
/-- (2.4) (commutative version only)
@isnad1 id=eq.2h4v.s8.d8a3caa2b6ce from=translated src=- shape=8e84e887 vocab=9761ea5c
-/
theorem Eq4 (x) : f x * f (x * 2 - 1) = (f (x - 1) + 1) * f (x * 2 + 1) := by
  have h0 : x * (x + 1) - 1 = (x - 1) * (x + 1 + 1) + 1 := by
    rw [mul_add_one (x - 1), add_assoc, sub_add_cancel, sub_one_mul,
      ← add_sub_right_comm, add_comm, add_sub_add_right_eq_sub]
  apply congrArg f at h0
  rw [Eq1 hf h, hf.is_good, sub_add_cancel_left, h, hf.map_one, sub_add_add_cancel,
    add_zero, add_assoc, one_add_one_eq_two, ← add_assoc, ← mul_two] at h0
  rw [Eq2 hf, mul_add, h0, ← add_assoc, add_one_mul (f _),
    add_left_inj, mul_left_comm, ← mul_add, ← hf.is_good]

omit [NoZeroDivisors S] in
/-- (2.4), alternate version
@isnad1 id=eq.2h4v.s8.87a526a8a37c from=translated src=- shape=61da7a24 vocab=9761ea5c
-/
theorem Eq4_alt (x) : f x * f (x * 2 + 1) = (f (x + 1) + 1) * f (x * 2 - 1) := by
  have h0 := Eq4 hf h (-x)
  rwa [h, neg_mul, ← neg_add', h, ← neg_add', h, neg_add_eq_sub, ← neg_sub, h] at h0

/-- `R` has characteristic `2` if `f(2) = -1`
@isnad1 id=eq.3h4v.s7.a97a2b30500a from=translated src=- shape=27a2b2f5 vocab=ac78388e
-/
theorem two_periodic_of_map_two (h0 : f 2 = -1) : ∀ x, f (x + 2) = f x :=
  have h1 (x) : f (x * 2 + 1) = f (x + 2) - f x := by
    rw [hf.is_good, h0, mul_neg_one, neg_add_eq_sub]
  have h2 (x) : f (x * 2 + 1) = -f (x * 2 - 1) := by
    rw [Eq2 hf, Eq3 hf h, h0, mul_neg_one, mul_neg_one, neg_add_rev, neg_neg]
  ---- First get the main ineq
  have h3 (x) : f x + f (x + 1) = -1 ∨ f (x * 2 - 1) = 0 := by
    have h3 := Eq4_alt hf h x
    rw [h2, mul_neg, neg_eq_iff_add_eq_zero, ← add_mul, mul_eq_zero, ← add_assoc] at h3
    exact h3.imp_left eq_neg_of_add_eq_zero_left
  ---- Now
  λ x ↦ (h3 (x + 1)).symm.elim
    (λ h4 ↦ by rwa [mul_two, add_sub_assoc, add_sub_cancel_right,
      add_right_comm, ← mul_two, h1, sub_eq_zero] at h4)
    λ h4 ↦ (h3 x).symm.elim
      (λ h5 ↦ by rwa [← neg_eq_zero, ← h2, h1, sub_eq_zero] at h5)
      (λ h5 ↦ by rwa [← h5, add_comm, add_left_inj, add_assoc, one_add_one_eq_two] at h4)

omit [CommRing S] [NoZeroDivisors S] hf h in
/--
@isnad1 id=eq.0h5v.s8.67c8b212150c from=translated src=- shape=14696cac vocab=26b25aee
-/
theorem Eq6_ring_id {S} [CommRing S] (a b c d : S) :
    a * (c * d + b) - a * (b * d + c) - ((c + 1) * (b * d + c) - (b + 1) * (c * d + b))
      = (b + c - (a + 1) * (d - 1)) * (b - c) := by ring

/-- (2.6), commutative case
@isnad1 id=eq.3h4v.s8.38e216fb2515 from=translated src=- shape=0d011f79 vocab=6297a92d
-/
theorem Eq6 (h0 : f 2 ≠ -1) : ∀ x, f (x + 1) + f (x - 1) = (f x + 1) * (f 2 - 1) := by
  ---- First, either the goal holds or `f(x + 1) = f(x - 1)`
  have h1 (x) : f (x + 1) + f (x - 1) = (f x + 1) * (f 2 - 1) ∨ f (x + 1) = f (x - 1) := by
    have h1 : _ - _ = _ - _ := congrArg₂ (· - ·) (Eq4 hf h x) (Eq4_alt hf h x)
    rw [Eq2 hf, Eq3 hf h, ← sub_eq_zero, Eq6_ring_id, mul_eq_zero] at h1
    exact h1.imp eq_of_sub_eq_zero eq_of_sub_eq_zero
  ---- Continue
  intro x; refine (h1 x).elim id λ h2 ↦ ?_
  specialize h1 (x + 1)
  rw [add_sub_cancel_right, add_assoc, one_add_one_eq_two] at h1
  rcases h1 with h1 | h1
  · have h2 := Eq3 hf h x
    rw [hf.is_good, eq_sub_of_add_eq h1, add_sub_left_comm, ← mul_sub_one,
      add_one_mul (f _), add_assoc, ← one_add_mul (f x), mul_sub_one,
      ← add_sub_right_comm, add_sub_assoc, add_right_inj, add_comm] at h2
    exact (eq_add_of_sub_eq' h2).symm
  · have h0 : f 2 + 1 ≠ 0 := λ X ↦ h0 (eq_neg_of_add_eq_zero_left X)
    have h3 := Eq3 hf h x
    rw [← h2, hf.is_good, h1, ← mul_add_one (f x), ← mul_add_one (f _),
      ← sub_eq_zero, ← sub_mul, mul_eq_zero, or_iff_left h0, sub_eq_zero] at h3
    have h4 := Eq4 hf h x
    rw [Eq3 hf h, Eq2 hf, ← h2, ← h3, ← sub_eq_zero, ← sub_mul, sub_add_cancel_left,
      neg_one_mul, neg_eq_zero, ← mul_add_one (f x), mul_eq_zero, or_iff_left h0] at h4
    rw [eq_comm, h4] at h3; rw [eq_comm, h3] at h2
    have h5 := Eq5 hf h h4 h3 0
    rw [zero_add, hf.is_good, add_comm 2 x, h1, h4, mul_zero,
      add_zero, hf.map_zero, eq_comm, neg_eq_zero] at h5
    rw [← sub_eq_zero, ← one_mul (_ - _), h5, zero_mul]

/-- (2.7), commutative case
@isnad1 id=eq.4h4v.s8.f26a8fd2593a from=translated src=- shape=5451e3c1 vocab=d3283b6b
-/
theorem Eq7 (h0 : f 2 ≠ -1) (h1 : f 2 ≠ 1) (x) :
    (f (x + 1) + 1) * (f (x - 1) + 1) = f x ^ 2 := by
  ---- Reduce to the case where `f(2x + 1) = f(2x - 1) = 0`
  have h2 : _ * _ = _ * _ := congrArg (f x * ·) (Eq4_alt hf h x)
  rw [← mul_assoc, ← sq, mul_left_comm, Eq4 hf h,
    ← mul_assoc, ← sub_eq_zero, ← sub_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2; exact (eq_of_sub_eq_zero h2).symm
  have h3 : _ * _ = _ * _ := congrArg (f x * ·) (Eq4 hf h x)
  rw [← mul_assoc, ← sq, mul_left_comm, Eq4_alt hf h,
    ← mul_assoc, ← sub_eq_zero, ← sub_mul, mul_eq_zero] at h3
  rcases h3 with h3 | h3; rwa [sub_eq_zero, eq_comm, mul_comm] at h3
  ---- Solve the case where `f(2x + 1) = f(2x - 1) = 0`
  rw [Eq3 hf h] at h2
  replace h3 : _ + _ = _ + _ := congrArg₂ (· + ·) h2 h3
  rw [Eq2 hf, add_add_add_comm, add_zero, ← add_mul,
    add_comm (f _), ← mul_add_one (α := S), mul_eq_zero,
    or_iff_left (h0 ∘ eq_neg_of_add_eq_zero_left), ← eq_neg_iff_add_eq_zero] at h3
  have X : f 2 - 1 ≠ 0 := h1 ∘ eq_of_sub_eq_zero
  rw [h3, ← sub_eq_add_neg, ← mul_sub_one, mul_eq_zero, or_iff_left X] at h2
  rw [h2, neg_zero] at h3
  have h4 := Eq6 hf h h0 x
  rw [h2, h3, add_zero, zero_eq_mul, or_iff_left X] at h4
  rw [h2, h3, zero_add, one_mul, eq_neg_of_add_eq_zero_left h4, neg_one_sq]

end CommCase

/-! ### Restriction to the case `f(2) ≠ -1` -/

structure GoodCase2 [NonAssocRing R] [NonAssocRing S] (f : R → S) : Prop
    extends NontrivialGood f where
  map_even : ∀ x, f (-x) = f x
  map_two_ne_neg_one : f 2 ≠ -1

structure RGoodCase2 [NonAssocRing R] [NonAssocRing S] (f : R → S) : Prop
    extends ReducedGood f, GoodCase2 f

namespace GoodCase2

variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R → S} (hf : GoodCase2 f)
include hf

/--
@isnad1 id=ne.1h3v.s5.7b508f5bc8d9 from=translated src=- shape=d57794ff vocab=0b4b4d2d
-/
theorem Rtwo_ne_zero : (2 : R) ≠ 0 :=
  λ h ↦ hf.map_two_ne_neg_one <| by rw [h, hf.map_zero]

/--
@isnad1 id=eq.1h5v.s6.cc5fea176dda from=translated src=- shape=0f7a5a71 vocab=b7a804fc
-/
theorem Eq1 : ∀ x y, f (x * y - 1) = f x * f y + f (x - y) :=
  Case2.Eq1 hf.toNontrivialGood hf.map_even

/-- (2.2)
@isnad1 id=eq.1h4v.s7.6fa3d6b33c71 from=translated src=- shape=60541a81 vocab=cadea5f9
-/
theorem Eq2 : ∀ x, f (x * 2 - 1) = f (x - 1) * f 2 + f (x + 1) :=
  Case2.Eq2 hf.toNontrivialGood

/-- (2.3)
@isnad1 id=eq.1h4v.s7.ce0c05e38615 from=translated src=- shape=615c5181 vocab=cadea5f9
-/
theorem Eq3 : ∀ x, f (x * 2 + 1) = f (x + 1) * f 2 + f (x - 1) :=
  Case2.Eq3 hf.toNontrivialGood hf.map_even

variable [NoZeroDivisors S]

end GoodCase2

/-! ### Subcase 2.1: `f(2) = 1`, `char(S) ∤ 2` -/

/-! ### Subcase 2.2: `f(2) = 0`, `char(S) ∤ 3` -/

namespace RGoodSubcase22

variable [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S} (hf : RGoodCase2 f) (h : f 2 = 0)
include hf h

end RGoodSubcase22

/-! ### Structure for Subcase 2.3: `f(2) = 3`, `char(S) ∤ 2` -/

/-- Structure expressing that `g - 1` is good and `(g - 1)(2) = 3` -/
structure ShiftGood23 [NonAssocRing R] [NonAssocRing S] (g : R → S) : Prop where
  shift_good : GoodCase2 (g - 1)
  map_two : g 2 = 4

namespace ShiftGood23

section

variable [NonAssocRing R] [NonAssocRing S]

/--
@isnad1 id=iff.0h3v.s6.7df9c4211a12 from=translated src=- shape=5cd34360 vocab=8a4c69c5
-/
lemma mk_iff {g : R → S} : ShiftGood23 g ↔ GoodCase2 (g - 1) ∧ g 2 = 4 :=
  ⟨λ ⟨h, h0⟩ ↦ ⟨h, h0⟩, λ ⟨h, h0⟩ ↦ ⟨h, h0⟩⟩

/--
@isnad1 id=iff.0h3v.s6.ef65ab2f641f from=translated src=- shape=062ae93c vocab=5432e076
-/
lemma shift_mk_iff {f : R → S} : ShiftGood23 (f + 1) ↔ GoodCase2 f ∧ f 2 = 3 := by
  rw [mk_iff, add_sub_cancel_right, ← three_add_one_eq_four]
  exact and_congr_right' (add_left_inj _)

variable {g : R → S} (hg : ShiftGood23 g)
include hg

/--
@isnad1 id=eq.1h3v.s5.75465427395d from=translated src=- shape=dbc7dfb6 vocab=5e04d2fe
-/
lemma map_zero : g 0 = 0 :=
  sub_eq_neg_self.mp hg.shift_good.map_zero

/--
@isnad1 id=eq.1h3v.s5.689e48a2fa60 from=translated src=- shape=dbc7dfb6 vocab=5e04d2fe
-/
lemma map_one : g 1 = 1 :=
  eq_of_sub_eq_zero hg.shift_good.map_one

/--
@isnad1 id=eq.1h4v.s5.d2bc83d23566 from=translated src=- shape=93cff077 vocab=b9777940
-/
lemma map_even (x) : g (-x) = g x :=
  sub_left_injective (hg.shift_good.map_even x)

/--
@isnad1 id=ne.1h3v.s5.85c1281f5c1d from=translated src=- shape=a8be3967 vocab=a54c3062
-/
lemma Schar_ne_two : (2 : S) ≠ 0 :=
  λ h ↦ hg.shift_good.map_two_ne_neg_one <| by
    rw [Pi.sub_apply, Pi.one_apply, sub_eq_neg_self, hg.map_two, ← three_add_one_eq_four,
      ← two_add_one_eq_three, h, zero_add, one_add_one_eq_two, h]

/--
@isnad1 id=eq.1h5v.s7.341a31852a70 from=translated src=- shape=3a7f4c9a vocab=d236aa10
-/
lemma is_good (x y) : g (x * y + 1) = (g x - 1) * (g y - 1) + g (x + y) := by
  have h := hg.shift_good.is_good x y
  simp only [Pi.sub_apply, Pi.one_apply] at h
  rwa [← add_sub_assoc, sub_left_inj] at h

/--
@isnad1 id=eq.1h5v.s7.00d5d9d80758 from=translated src=- shape=ff99971c vocab=d236aa10
-/
lemma alt_good (x y) : g (x * y - 1) = (g x - 1) * (g y - 1) + g (x - y) := by
  have h := hg.is_good x (-y)
  rwa [hg.map_even, mul_neg, neg_add_eq_sub, ← neg_sub, hg.map_even, ← sub_eq_add_neg] at h

end

section

variable [Ring R] [Ring S] [NoZeroDivisors S] {g : R → S} (hg : ShiftGood23 g)
include hg

omit [NoZeroDivisors S] in
/-- (2.3.2)
@isnad1 id=eq.1h5v.s7.b98b3a1a0409 from=translated src=- shape=4ff7993e vocab=5d41f1c4
-/
lemma Eq2 (x y) : g (x * y + 1) - g (x * y - 1) = g (x + y) - g (x - y) := by
  rw [hg.is_good, hg.alt_good, add_sub_add_left_eq_sub]

omit [Ring S] [NoZeroDivisors S] hg in

end

end ShiftGood23

structure RShiftGood23 [NonAssocRing R] [NonAssocRing S] (g : R → S) : Prop
  extends RGoodCase2 (g - 1), ShiftGood23 g

namespace RShiftGood23

section

variable [NonAssocRing R] [NonAssocRing S]

/--
@isnad1 id=iff.0h3v.s6.b637b2eee67f from=translated src=- shape=5cd34360 vocab=f6842764
-/
lemma mk_iff {g : R → S} : RShiftGood23 g ↔ RGoodCase2 (g - 1) ∧ g 2 = 4 :=
  ⟨λ ⟨h, h0⟩ ↦ ⟨h, (ShiftGood23.mk_iff.mp h0).2⟩, λ ⟨h, h0⟩ ↦ ⟨h, h.toGoodCase2, h0⟩⟩

/--
@isnad1 id=iff.0h3v.s6.788b0fcaed68 from=translated src=- shape=062ae93c vocab=96be18a2
-/
lemma shift_mk_iff {f : R → S} : RShiftGood23 (f + 1) ↔ RGoodCase2 f ∧ f 2 = 3 := by
  rw [mk_iff, add_sub_cancel_right, ← three_add_one_eq_four]
  exact and_congr_right' (add_left_inj _)

variable {g : R → S} (hg : RShiftGood23 g)
include hg

/--
@isnad1 id=eq.2h5v.s6.d8a36cabdcca from=translated src=- shape=9b896a55 vocab=09ba0ba1
-/
lemma period_imp_eq₀ (c d) (h : ∀ x, g (x + c) = g (x + d)) : c = d :=
  hg.period_imp_eq c d λ x ↦ congrArg₂ (· - ·) (h x) rfl

/--
@isnad1 id=eq.2h4v.s6.3cc85b48fa7a from=translated src=- shape=5491317d vocab=09ba0ba1
-/
lemma period_imp_zero₀ {c} (h : ∀ x, g (x + c) = g x) : c = 0 :=
  hg.period_imp_eq₀ c 0 λ x ↦ by rw [h, add_zero]

end

section

variable {R : Type u} [Ring R] [Ring S] [NoZeroDivisors S] {g : R → S} (hg : RShiftGood23 g)
include hg

open Extra.SquareLike

end

end RShiftGood23

/-! ### Summary -/

section

variable {R : Type u} [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S}
