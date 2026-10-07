/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Ring.Subsemiring.Defs
public import Tengoku.Seed.RingTheory.Ideal.Prime
public import Tengoku.Seed.Algebra.Group.Pointwise.Set.Basic

/-!
# Ring orderings

Let `R` be a commutative ring. A preordering on `R` is a subset closed under
addition and multiplication that contains all squares, but not `-1`.

The support of a preordering `P` is the set of elements `x` such that both `x` and `-x` lie in `P`.

An ordering `O` on `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.

We define preorderings, supports and orderings.

A ring preordering can intuitively be viewed as a set of "non-negative" ring elements.
Indeed, an ordering `O` with support `p` induces a linear order on `R⧸p` making it
into an ordered ring, and vice versa.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

/-!
#### Preorderings
-/

variable (R : Type*) [CommRing R]

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
@[ext]
structure RingPreordering extends Subsemiring R where
  mem_of_isSquare' {x : R} (hx : IsSquare x) : x ∈ carrier := by aesop
  neg_one_notMem' : -1 ∉ carrier := by aesop

namespace RingPreordering

attribute [coe] toSubsemiring

instance : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance : PartialOrder (RingPreordering R) := .ofSetLike (RingPreordering R) R

initialize_simps_projections RingPreordering (carrier → coe, as_prefix coe)

instance : SubsemiringClass (RingPreordering R) R where
  zero_mem _ := Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

variable {R}

/--
@isnad1 id=mem.1h3v.s5.b85b9a045791 from=seed src=0 shape=19141381 vocab=982f8b63
-/
@[aesop unsafe 80% (rule_sets := [SetLike])]
protected theorem mem_of_isSquare (P : RingPreordering R) {x : R} (hx : IsSquare x) : x ∈ P :=
  RingPreordering.mem_of_isSquare' _ hx

/--
@isnad1 id=mem.0h3v.s5.45091ee8f9ee from=seed src=0 shape=9b8db8d8 vocab=64e3ecc0
-/
@[simp]
protected theorem mul_self_mem (P : RingPreordering R) (x : R) : x * x ∈ P := by aesop

/--
@isnad1 id=mem.0h3v.s5.cb4e8e5cba85 from=seed src=0 shape=442959a7 vocab=b608f4ce
-/
@[simp]
protected theorem pow_two_mem (P : RingPreordering R) (x : R) : x ^ 2 ∈ P := by aesop

/--
@isnad1 id=not.0h2v.s5.47169c6c4bff from=seed src=0 shape=fc0aad28 vocab=97978a8b
-/
@[aesop unsafe 20% forward (rule_sets := [SetLike])]
protected theorem neg_one_notMem (P : RingPreordering R) : -1 ∉ P :=
  RingPreordering.neg_one_notMem' _

/--
@isnad1 id=injectiv.0h1v.s4.46062f83eacb from=seed src=0 shape=e716c754 vocab=37f527e3
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R → _) := fun A B h => by ext; rw [h]

/--
@isnad1 id=iff.0h3v.s5.d659f6869f8d from=seed src=0 shape=49a1ec5b vocab=b7594d03
-/
@[simp]
theorem toSubsemiring_inj {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := toSubsemiring_injective.eq_iff

/--
@isnad1 id=iff.0h3v.s5.5b8c3079d48e from=seed src=0 shape=51b12b4b vocab=fe032df3
-/
@[simp]
theorem mem_toSubsemiring {P : RingPreordering R} {x : R} : x ∈ P.toSubsemiring ↔ x ∈ P := .rfl

/--
@isnad1 id=eq.0h2v.s5.bac1915247ac from=seed src=0 shape=33410fb1 vocab=6d0eb6dc
-/
@[simp, norm_cast]
theorem coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P := rfl

/--
@isnad1 id=iff.2h3v.s7.1bce58452f73 from=seed src=0 shape=180376f1 vocab=e5719a57
-/
@[simp]
theorem mem_mk {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x : R} :
    x ∈ mk toSubsemiring mem_of_isSquare neg_one_notMem ↔ x ∈ toSubsemiring := .rfl

/--
@isnad1 id=eq.2h2v.s7.22fd5740de4d from=seed src=0 shape=fcc1710d vocab=a8e20352
-/
@[simp]
theorem coe_set_mk (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem) :
    (mk toSubsemiring mem_of_isSquare neg_one_notMem : Set R) = toSubsemiring := rfl

section copy

variable (P : RingPreordering R) (S : Set R) (hS : S = P)

/-- Copy of a preordering with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
protected def copy : RingPreordering R where
  carrier := S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop

attribute [norm_cast] coe_copy
/--
@isnad1 id=iff.1h4v.s5.1477bf2b984a from=seed src=0 shape=c42d3e76 vocab=19d2771c
-/
@[simp] theorem mem_copy {x} : x ∈ P.copy S hS ↔ x ∈ S := .rfl
/--
@isnad1 id=eq.1h3v.s5.21993b569e9a from=seed src=0 shape=048308b0 vocab=93d4ed86
-/
theorem copy_eq : P.copy S hS = S := rfl

end copy

variable {P : RingPreordering R}

/-!
#### Support
-/

section supportAddSubgroup

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def supportAddSubgroup : AddSubgroup R where
  carrier := P ∩ -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

/--
@isnad1 id=iff.0h3v.s6.b477a64fa2c4 from=seed src=0 shape=1cceee47 vocab=6a79a9a1
-/
theorem mem_supportAddSubgroup {x} : x ∈ P.supportAddSubgroup ↔ x ∈ P ∧ -x ∈ P := .rfl
/--
@isnad1 id=eq.0h2v.s6.676c9a089dce from=seed src=0 shape=d988b5d4 vocab=e4243d2c
-/
theorem coe_supportAddSubgroup : P.supportAddSubgroup = (P ∩ -P : Set R) := rfl

end supportAddSubgroup

/-- Typeclass to track whether the support of a preordering forms an ideal. -/
class HasIdealSupport (P : RingPreordering R) : Prop where
  smul_mem_support (P) (x : R) {a : R} (ha : a ∈ P.supportAddSubgroup) :
    x * a ∈ P.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

/--
@isnad1 id=iff.0h2v.s7.a4557c4f4a77 from=seed src=0 shape=3d5e388e vocab=a9dbe29f
-/
theorem hasIdealSupport_iff :
    P.HasIdealSupport ↔ ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P where
  mp _ := by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

instance [HasMemOrNegMem P] : P.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

section support

variable [P.HasIdealSupport]

variable (P) in
/--
The support of a ring preordering `P` in a commutative ring `R` is
the set of elements `x` in `R` such that both `x` and `-x` lie in `P`.
-/
def support : Ideal R where
  __ := P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P

/--
@isnad1 id=iff.0h3v.s6.e46cd0222ee6 from=seed src=0 shape=4277882c vocab=db0e3ef7
-/
theorem mem_support {x} : x ∈ P.support ↔ x ∈ P ∧ -x ∈ P := .rfl
/--
@isnad1 id=eq.0h2v.s6.b3204293e9d9 from=seed src=0 shape=ff843f5a vocab=fffa3753
-/
theorem coe_support : P.support = (P : Set R) ∩ -(P : Set R) := rfl

/--
@isnad1 id=eq.0h2v.s5.a8178ffdd622 from=seed src=0 shape=ca435909 vocab=a2778b0f
-/
@[simp] theorem supportAddSubgroup_eq : P.supportAddSubgroup = P.support.toAddSubgroup := rfl

end support

/--
An ordering `O` on a ring `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.
-/
class IsOrdering (P : RingPreordering R) extends HasMemOrNegMem P, P.support.IsPrime

end RingPreordering
