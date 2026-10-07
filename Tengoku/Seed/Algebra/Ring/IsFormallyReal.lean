/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Ring.SumsOfSquares
public import Tengoku.Seed.RingTheory.Nilpotent.Basic

/-!
# Formally real rings

A ring `R` is *formally real* if, whenever `∑ i, x i ^ 2 = 0`, in fact `x i = 0` for all `i`.

We define formally real rings in an index-free manner using the inductive predicate
`IsSumNonzeroSq`, which asserts that an element is a finite sum of squares of nonzero elements.
A ring is then formally real if `¬ IsSumNonzeroSq 0`.

## Main declaration

- `IsFormallyReal`: typeclass stating that a ring is formally real.

-/

@[expose] public section

variable {R : Type*}

section IsSumNonzeroSq

/--
The property of being a sum of squares of nonzero elements (S) is defined inductively by:
`a * a : R` is (S) for all nonzero `a`, and
if `s : R` is (S), and `a ≠ 0`, then `a * a + s` is (S).
-/
@[mk_iff]
inductive IsSumNonzeroSq [Mul R] [Add R] [Zero R] : R → Prop
  | sq {a : R} (ha : a ≠ 0) : IsSumNonzeroSq (a * a)
  | sq_add {a s : R} (ha : a ≠ 0) (hs : IsSumNonzeroSq s) : IsSumNonzeroSq (a * a + s)

attribute [aesop 90%] IsSumNonzeroSq.sq

/--
@isnad1 id=issumnon.2h3v.s6.c1c14c500a3b from=seed src=0 shape=110fb96e vocab=c67ca440
-/
@[aesop 90%]
theorem IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [sq_add, add_assoc]

/--
@isnad1 id=issumsq.1h2v.s5.ef4fd4e9fcba from=seed src=0 shape=b0c8cbfb vocab=b61ef718
-/
theorem IsSumNonzeroSq.isSumSq [AddMonoid R] [Mul R] {s : R}
    (h : IsSumNonzeroSq s) : IsSumSq s := by
  induction h <;> aesop

/--
@isnad1 id=iff.1h2v.s5.951ecbb72e9c from=seed src=0 shape=e66e10b0 vocab=42e290e1
-/
theorem isSumNonzeroSq_iff_isSumSq [NonUnitalNonAssocSemiring R] {s : R} (hs : s ≠ 0) :
    IsSumNonzeroSq s ↔ IsSumSq s where
  mp := IsSumNonzeroSq.isSumSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)

/--
@isnad1 id=issumnon.2h2v.s5.e72213220cec from=seed src=0 shape=fb0fdeef vocab=42e290e1
-/
alias ⟨_, IsSumSq.isSumNonzeroSq_of_ne_zero⟩ := isSumNonzeroSq_iff_isSumSq

namespace AddSubsemigroup

variable [AddMonoid R] [Mul R] {s : R}

variable (R) in
/-- The subsemigroup of sums of squares of nonzero elements. -/
@[simps]
def sumNonzeroSq : AddSubsemigroup R where
  carrier := {s : R | IsSumNonzeroSq s}
  add_mem' := .add

attribute [norm_cast] coe_sumNonzeroSq

/--
@isnad1 id=iff.0h2v.s5.94a3cb1aa262 from=seed src=0 shape=1335d7f0 vocab=8949b270
-/
@[simp] theorem mem_sumNonzeroSq : s ∈ sumNonzeroSq R ↔ IsSumNonzeroSq s := .rfl

/--
@isnad1 id=eq.0h1v.s5.80f2565e8f48 from=seed src=0 shape=f8f9700e vocab=c3e1a027
-/
@[simp]
theorem closure_mul_self : closure {x * x | x ≠ (0 : R)} = sumNonzeroSq R := by
  refine closure_eq_of_le (fun x hx ↦ by aesop) (fun x hx ↦ ?_)
  -- TODO : fix aesop timeout and change to `induction hx <;> aesop`
  induction hx with
  | sq ha => aesop
  | sq_add ha hs ih =>
    -- `aesop` times out
    apply add_mem
    · apply AddSubsemigroup.mem_closure_of_mem
      aesop
    aesop

end AddSubsemigroup

end IsSumNonzeroSq

variable (R) in
/--
A ring is formally real if, whenever `∑ i, x i ^ 2 = 0`, we in fact have `x i = 0` for all `i`.
-/
class IsFormallyReal [AddCommMonoid R] [Mul R] : Prop where
  not_isSumNonzeroSq_zero : ¬ IsSumNonzeroSq (0 : R)

namespace IsFormallyReal

/--
@isnad1 id=isformal.2h1v.s7.d0e0eb9838ab from=seed src=0 shape=b926ab60 vocab=4ce84ea2
-/
theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {s₁ s₂ : R}, IsSumSq s₁ → IsSumSq s₂ → s₁ + s₂ = 0 → s₁ = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) hs.isSumSq]

/--
@isnad1 id=isformal.1h1v.s6.f55070d00c31 from=seed src=0 shape=00079be2 vocab=2f8dbc89
-/
theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : ∀ {s a : R}, IsSumSq s → a * a + s = 0 → a = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc ↦ ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [hs.isSumSq]

instance [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R :=
  of_eq_zero_of_mul_self_of_eq_zero_of_add mul_self_eq_zero.mp <|
    fun hs₁ hs₂ h ↦ ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1

instance [Ring R] [IsFormallyReal R] : IsReduced R := by
  rw [isReduced_iff_pow_one_lt 2 (by lia)]
  intro x hx
  by_contra! hc
  exact not_isSumNonzeroSq_zero <| by simpa [← pow_two, hx] using IsSumNonzeroSq.sq hc

theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  by_contra! h₁
  have h₂ : s₂ ≠ 0 := fun hc ↦ by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)

theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0 := by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]

theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 :=
  eq_zero_of_add_right h₁ h₂ (by simp)

end IsFormallyReal
