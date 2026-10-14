/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Generalization.IMO2012A5.A5Defs
public import Tengoku

/-!
# IMO 2012 A5 (Quasi-periodic elements)

Let `R` be a ring, `S` be a domain, and `f : R → S` be a non-trivial good function.
Consider the set `J = {c | ∀ x, f(c + x) = -f(c) f(x)}`.
We prove that `J` is a two-sided ideal, implemented by `QuasiPeriodic`.
We prove some more properties:
* `QuasiPeriodic.iff_right`: `c ∈ J ↔ ∀ x, f (x + c) = -f(x) f(c)`,
* `QuasiPeriodic.reduced_main_cases`: Let `f` be a reduced good function.
  If there exists `c ∈ J` non-zero, then `R = {0, 1, c, c + 1}`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

/-- A symmetric definition of quasi-periodic. Convenient, since we need
  both versions to prove that the set of periods form a double-sided ideal.
  Note that the two versions are equivalent on non-zero good functions. -/
inductive QuasiPeriodic [Add R] [Neg S] [Mul S] (f : R → S) (c : R) : Prop
  | Left : (∀ x, f (c + x) = -f c * f x) → QuasiPeriodic f c
  | Right : (∀ x, f (x + c) = f x * -f c) → QuasiPeriodic f c

namespace QuasiPeriodic

section

variable [NonAssocRing R] [NonAssocRing S] [NoZeroDivisors S]
  {f : R → S} (hf : NontrivialGood f) {c} (h : QuasiPeriodic f c)
include hf h

omit [NoZeroDivisors S] in
/--
@isnad1 id=eq.2h4v.s6.8e7e23b108bf from=translated src=- shape=e4e78914 vocab=b773fd1b
-/
theorem map_neg : f (-c) = f c := by
  have h0 : f (c + 1) = 0 := by cases h with
  | Left h => rw [h, hf.map_one, mul_zero]
  | Right h => rw [add_comm, h, hf.map_one, zero_mul]
  have h1 := hf.is_good (c + 1) (-1)
  rwa [h0, zero_mul, zero_add, add_neg_cancel_right,
    mul_neg_one, neg_add_rev, neg_add_cancel_comm] at h1

omit [NoZeroDivisors S] in
/--
@isnad1 id=eq.2h4v.s7.b5437aebfd5f from=translated src=- shape=6db1218c vocab=265902e4
-/
theorem map_mul_self_eq_one : f c * f c = 1 :=
  have h0 : f (-c) = f c := map_neg hf h
  have h1 : f 0 = -(f c * f c) := by cases h with
  | Left h => specialize h (-c); rwa [add_neg_cancel, h0, neg_mul] at h
  | Right h => specialize h (-c); rwa [neg_add_cancel, h0, mul_neg] at h
  by rwa [hf.map_zero, neg_inj, eq_comm] at h1

/--
@isnad1 id=or.2h4v.s7.b7a8113302e9 from=translated src=- shape=c0383e26 vocab=ee5ea111
-/
theorem map_eq_one_or_neg_one : f c = 1 ∨ f c = -1 :=
  mul_self_eq_one_iff.mp (map_mul_self_eq_one hf h)

private theorem map_commute (x : R) : Commute (-f c) (f x) := by
  cases map_eq_one_or_neg_one hf h with
  | inl h => rw [h]; exact Commute.neg_one_left (f x)
  | inr h => rw [h, neg_neg]; exact Commute.one_left (f x)

/--
@isnad1 id=eq.2h5v.s7.9c8836dc5bee from=translated src=- shape=5f33eb38 vocab=ddd53483
-/
theorem imp_left : ∀ x, f (c + x) = -f c * f x :=
  h.casesOn id λ h0 x ↦ by rw [add_comm, h0, map_commute hf h]

/--
@isnad1 id=eq.2h5v.s7.a98d4c41d982 from=translated src=- shape=941d5ea3 vocab=ddd53483
-/
theorem imp_right : ∀ x, f (x + c) = f x * -f c :=
  h.casesOn (λ h0 x ↦ by rw [add_comm, h0, map_commute hf h]) id

omit h in
/--
@isnad1 id=iff.1h4v.s7.5ef08846412b from=translated src=- shape=d7497017 vocab=ddd53483
-/
theorem iff_left : QuasiPeriodic f c ↔ ∀ x, f (c + x) = -f c * f x :=
  ⟨QuasiPeriodic.imp_left hf, QuasiPeriodic.Left⟩

omit h in
/--
@isnad1 id=iff.1h4v.s7.d98e1539a4a0 from=translated src=- shape=0975f1d8 vocab=ddd53483
-/
theorem iff_right : QuasiPeriodic f c ↔ ∀ x, f (x + c) = f x * -f c :=
  ⟨QuasiPeriodic.imp_right hf, QuasiPeriodic.Right⟩

omit h in
/--
@isnad1 id=iff.1h4v.s7.a24eff957e27 from=translated src=- shape=49dba4e6 vocab=457e6d6e
-/
theorem iff_left2 : QuasiPeriodic f c ↔ ∀ x, f (c * x + 1) = 0 :=
  (iff_left hf).trans <| forall_congr' λ x ↦ by
    rw [neg_mul, hf.is_good, eq_neg_iff_add_eq_zero, add_comm]

omit h in
/--
@isnad1 id=iff.1h4v.s7.c21af3d8ab76 from=translated src=- shape=b3f6b545 vocab=457e6d6e
-/
theorem iff_right2 : QuasiPeriodic f c ↔ ∀ x, f (x * c + 1) = 0 :=
  (iff_right hf).trans <| forall_congr' λ x ↦ by
    rw [mul_neg, hf.is_good, eq_neg_iff_add_eq_zero, add_comm]

end

section

variable [Ring R] [NonAssocRing S] [NoZeroDivisors S]
  {f : R → S} (hf : NontrivialGood f) {c} (h : QuasiPeriodic f c)
include hf h

/--
@isnad1 id=quasiper.2h5v.s7.854e727c04be from=translated src=- shape=e551d2a9 vocab=6f0bcebd
-/
theorem mul_left (d : R) : QuasiPeriodic f (d * c) := by
  rw [iff_right2 hf] at h ⊢
  intro x; rw [← mul_assoc]; exact h (x * d)

/--
@isnad1 id=quasiper.2h5v.s7.e48a36173a65 from=translated src=- shape=37105643 vocab=6f0bcebd
-/
theorem mul_right (d : R) : QuasiPeriodic f (c * d) := by
  rw [iff_left2 hf] at h ⊢
  intro x; rw [mul_assoc]; exact h (d * x)

end

/-! ### Extra structure given a non-zero quasi-periodic element -/

section

variable [NonAssocRing R] [NonAssocRing S] [NoZeroDivisors S]
  {f : R → S} (hf : ReducedGood f) {c} (h : QuasiPeriodic f c) (h0 : c ≠ 0)
include hf h h0

omit h0 in
/--
@isnad1 id=iff.2h4v.s7.317ba5a47544 from=translated src=- shape=7516a809 vocab=61de805c
-/
theorem reduced_eq_zero_iff : c = 0 ↔ f c = -1 :=
  ⟨λ h0 ↦ h0 ▸ hf.map_zero, λ h0 ↦ hf.period_imp_eq c 0 λ x ↦ by
    rw [add_zero, (iff_right hf.toNontrivialGood).mp h, h0, neg_neg, mul_one]⟩

/--
@isnad1 id=eq.3h4v.s7.9f16b3a287d3 from=translated src=- shape=9a79318d vocab=fb774e63
-/
theorem reduced_map_eq_one : f c = 1 :=
  (map_eq_one_or_neg_one hf.toNontrivialGood h).resolve_right <|
    mt (reduced_eq_zero_iff hf h).mpr h0

/--
@isnad1 id=or.4h5v.s7.0d25ca58c50e from=translated src=- shape=864fbbb9 vocab=fb774e63
-/
theorem reduced_QuasiPeriodic_eq (h1 : QuasiPeriodic f d) : d = 0 ∨ d = c :=
  (map_eq_one_or_neg_one hf.toNontrivialGood h1).symm.imp
    ---- Case 1: `f(d) = -1`
    (reduced_eq_zero_iff hf h1).mpr
    ---- Case 2: `f(d) = 1`
    (λ h2 ↦ hf.period_imp_eq d c λ x ↦ by
      have h3 (c) := (iff_right hf.toNontrivialGood (c := c)).mp
      rw [h3 c h, h3 d h1, h2, reduced_map_eq_one hf h h0])

/--
@isnad1 id=quasiper.4h5v.s7.2a2942178df5 from=translated src=- shape=dbea7724 vocab=09d5928b
-/
theorem reduced_mul_left_eq_zero_imp {d} (h1 : d * c = 0) : QuasiPeriodic f d := by
  rw [iff_left2 hf.toNontrivialGood]; intro x
  have h2 := reduced_map_eq_one hf h h0
  have h3 : f (d * (c + x) + 1) = -f (d * x + 1) := by
    rw [iff_left hf.toNontrivialGood] at h
    rw [hf.is_good, h, add_left_comm, h, h2, neg_one_mul,
      neg_one_mul, mul_neg, ← neg_add, hf.is_good]
  rw [mul_add, h1, zero_add, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h3
  refine h3.resolve_left λ h3 ↦ h0 ?_
  rw [reduced_eq_zero_iff hf h, h2, eq_neg_iff_add_eq_zero, one_add_one_eq_two, h3]

end

section

variable [Ring R] [NonAssocRing S] [NoZeroDivisors S]
  {f : R → S} (hf : ReducedGood f) {c} (h : QuasiPeriodic f c) (h0 : c ≠ 0)
include hf h h0

/--
@isnad1 id=or.3h5v.s7.2cc0fa533bf1 from=translated src=- shape=bb7ae4af vocab=d1f74457
-/
theorem reduced_QuasiPeriod_equiv_cases (d) :
    QuasiPeriodic f d ∨ QuasiPeriodic f (d - 1) :=
  let h1 (d) := reduced_mul_left_eq_zero_imp hf h h0 (d := d)
  (reduced_QuasiPeriodic_eq hf h h0 <| mul_left hf.toNontrivialGood h d).imp
    (h1 d) (λ h2 ↦ h1 (d - 1) <| by rwa [sub_one_mul, sub_eq_zero])

/--
@isnad1 id=or.3h5v.s7.72d76088b195 from=translated src=- shape=b25db82e vocab=f9d277a1
-/
theorem reduced_main_cases (d) : (d = 0 ∨ d = c) ∨ (d = 1 ∨ d = c + 1) :=
  let h1 (d) := reduced_QuasiPeriodic_eq hf h h0 (d := d)
  (reduced_QuasiPeriod_equiv_cases hf h h0 d).imp
    (h1 d) (λ h2 ↦ (h1 _ h2).imp eq_of_sub_eq_zero eq_add_of_sub_eq)

end
