/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Field.IsField
public import Tengoku.Seed.Algebra.Order.Ring.Ordering.Defs
public import Tengoku.Seed.Algebra.Ring.SumsOfSquares
public import Tengoku.Seed.Tactic.FieldSimp
public import Tengoku.Seed.Tactic.LinearCombination
public import Tengoku.Seed.Tactic.Ring

/-!
# Ring orderings

We prove basic properties of (pre)orderings on rings and their supports.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {P : RingPreordering R}

/-!
### Preorderings
-/

namespace RingPreordering

/--
@isnad1 id=iff.0h3v.s6.5ccaa545b9d6 from=seed src=0 shape=49a1ec5b vocab=672fee33
-/
@[gcongr]
theorem toSubsemiring_le_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring ≤ P₂.toSubsemiring ↔ P₁ ≤ P₂ := .rfl

/--
@isnad1 id=iff.0h3v.s6.ba1bffa7cc94 from=seed src=0 shape=49a1ec5b vocab=dd178a1a
-/
@[gcongr]
theorem toSubsemiring_lt_toSubsemiring {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring < P₂.toSubsemiring ↔ P₁ < P₂ := .rfl

/--
@isnad1 id=monotone.0h1v.s5.66afb8ca5538 from=seed src=0 shape=e716c754 vocab=c8e8c483
-/
@[mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

/--
@isnad1 id=strictmo.0h1v.s5.2ff1ba3a67df from=seed src=0 shape=e716c754 vocab=29de2c41
-/
@[mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : RingPreordering R → _) :=
  fun _ _ => id

/--
@isnad1 id=mem.1h3v.s6.345847127e78 from=seed src=0 shape=d563c58e vocab=eb7905e5
-/
@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem unitsInv_mem {a : Rˣ} (ha : ↑a ∈ P) : ↑a⁻¹ ∈ P := by
  have : (a * (a⁻¹ * a⁻¹) : R) ∈ P := by aesop (config := { enableSimp := false })
  simp_all

/--
@isnad1 id=mem.1h3v.s6.42a0efb88c68 from=seed src=0 shape=990df938 vocab=bd9c5b94
-/
@[aesop unsafe 90% apply (rule_sets := [SetLike])]
theorem inv_mem {F : Type*} [Field F] {P : RingPreordering F} {a : F} (ha : a ∈ P) :
    a⁻¹ ∈ P := by
  have mem : a * (a⁻¹ * a⁻¹) ∈ P := by aesop
  field_simp at mem
  simp_all

/--
@isnad1 id=mem.1h3v.s5.3375d7da80c1 from=seed src=0 shape=19141381 vocab=eecc7731
-/
@[aesop unsafe 80% apply (rule_sets := [SetLike])]
theorem mem_of_isSumSq {x : R} (hx : IsSumSq x) : x ∈ P := by
  induction hx using IsSumSq.rec' <;> aesop

section mk'

variable {R : Type*} [CommRing R] {P : Set R} {add} {mul} {sq} {neg_one}

/-- Construct a preordering from a minimal set of axioms. -/
def mk' {R : Type*} [CommRing R] (P : Set R)
    (add : ∀ {x y : R}, x ∈ P → y ∈ P → x + y ∈ P)
    (mul : ∀ {x y : R}, x ∈ P → y ∈ P → x * y ∈ P)
    (sq : ∀ x : R, x * x ∈ P)
    (neg_one : -1 ∉ P) :
    RingPreordering R where
  carrier := P
  add_mem' {x y} := by simpa using add
  mul_mem' {x y} := by simpa using mul
  zero_mem' := by simpa using sq 0
  one_mem' := by simpa using sq 1

/--
@isnad1 id=iff.4h3v.s7.d6221021966e from=seed src=0 shape=a78b309a vocab=7187c761
-/
@[simp] theorem mem_mk' {x : R} : x ∈ mk' P add mul sq neg_one ↔ x ∈ P := .rfl
/--
@isnad1 id=eq.4h2v.s7.9beeda3b2df8 from=seed src=0 shape=2096c876 vocab=6ed18da1
-/
@[simp, norm_cast] theorem coe_mk' : mk' P add mul sq neg_one = P := rfl

end mk'

/-!
### Supports
-/

section ne_top

variable (P)

/--
@isnad1 id=not.0h2v.s5.49965ab39407 from=seed src=0 shape=966202e3 vocab=51e35ca5
-/
theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup :=
  fun h => RingPreordering.neg_one_notMem P h.2

/--
@isnad1 id=not.0h2v.s6.8b895bfd718f from=seed src=0 shape=2ae49914 vocab=2c795a1a
-/
theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using one_notMem_supportAddSubgroup P

/--
@isnad1 id=ne.0h2v.s5.20bb2885c831 from=seed src=0 shape=5a396c83 vocab=a2cb3984
-/
theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ :=
  fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2

/--
@isnad1 id=ne.0h2v.s5.4508bca4c1cf from=seed src=0 shape=566a6322 vocab=76e8c69d
-/
theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using supportAddSubgroup_ne_top P

/-- Constructor for IsOrdering that doesn't require `ne_top'`.
@isnad1 id=isorderi.1h2v.s7.7ff6cbb8160e from=seed src=0 shape=08f545e1 vocab=50b01520
-/
theorem IsOrdering.mk' [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := support_ne_top P
  mem_or_mem' := h

end ne_top

namespace HasIdealSupport

/--
@isnad1 id=mem.2h4v.s6.b968e2a0a0e1 from=seed src=0 shape=5532d407 vocab=a9dbe29f
-/
theorem smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : x * a ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

/--
@isnad1 id=mem.2h4v.s6.006e1ea5c0fc from=seed src=0 shape=b9002b91 vocab=a9dbe29f
-/
theorem neg_smul_mem [P.HasIdealSupport]
    (x : R) {a : R} (h₁a : a ∈ P) (h₂a : -a ∈ P) : -(x * a) ∈ P := by
  rw [hasIdealSupport_iff] at ‹P.HasIdealSupport›
  simp [*]

end HasIdealSupport

/--
@isnad1 id=hasideal.1h2v.s5.fe789b5d9e59 from=seed src=0 shape=aec7b3ab vocab=3d48046d
-/
theorem hasIdealSupport_of_isUnit_two (h : IsUnit (2 : R)) : P.HasIdealSupport := by
  rw [hasIdealSupport_iff]
  intro x a _ _
  rcases h.exists_right_inv with ⟨half, h2⟩
  set y := (1 + x) * half
  set z := (1 - x) * half
  rw [show x = y ^ 2 - z ^ 2 by
    linear_combination (-x - x * half * 2) * h2]
  ring_nf
  aesop (add simp sub_eq_add_neg)

instance [h : Fact (IsUnit (2 : R))] : P.HasIdealSupport := hasIdealSupport_of_isUnit_two h.out

section Field

variable {F : Type*} [Field F] (P : RingPreordering F)

variable {P} in
@[aesop unsafe 70% apply]
protected theorem eq_zero_of_mem_of_neg_mem {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

/--
@isnad1 id=eq.0h2v.s5.0249fb4f3666 from=seed src=0 shape=5a396c83 vocab=598554e9
-/
theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

instance : P.HasIdealSupport where
  smul_mem_support := by simp [supportAddSubgroup_eq_bot]

/--
@isnad1 id=eq.0h2v.s6.a3c23257d0e4 from=seed src=0 shape=5a396c83 vocab=98ed9568
-/
@[simp] theorem support_eq_bot : P.support = ⊥ := by
  simpa [← Submodule.toAddSubgroup_inj] using supportAddSubgroup_eq_bot P

instance : P.support.IsPrime := by simpa using Ideal.isPrime_bot

end Field

/--
@isnad1 id=iff.0h2v.s6.70e2f8881bd7 from=seed src=0 shape=bb38b9f3 vocab=6318f981
-/
theorem isOrdering_iff :
    P.IsOrdering ↔ ∀ a b : R, -(a * b) ∈ P → a ∈ P ∨ b ∈ P := by
  refine ⟨fun _ a b _ => ?_, fun h => ?_⟩
  · by_contra
    have : a * b ∈ P := by simpa using mul_mem (by aesop : -a ∈ P) (by aesop : -b ∈ P)
    have : a ∈ P.support ∨ b ∈ P.support :=
      Ideal.IsPrime.mem_or_mem inferInstance (by simp_all [mem_support])
    simp_all [mem_support]
  · have : HasMemOrNegMem P := ⟨by simp [h]⟩
    refine IsOrdering.mk' P (fun {x y} _ => ?_)
    by_contra
    have := h (-x) y
    have := h (-x) (-y)
    have := h x y
    have := h x (-y)
    cases (by aesop : x ∈ P ∨ -x ∈ P) <;> simp_all [mem_support]
end RingPreordering
