/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Idempotent
public import Tengoku.Seed.Algebra.Ring.Equiv
public import Tengoku.Seed.Algebra.Ring.PUnit
public import Tengoku.Seed.Order.Hom.BoundedLattice
public import Tengoku.Seed.Tactic.Abel
public import Tengoku.Seed.Tactic.Ring

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `BooleanRing`: a typeclass for rings where multiplication is idempotent.
* `BooleanRing.toBooleanAlgebra`: Turn a Boolean ring into a Boolean algebra.
* `BooleanAlgebra.toBooleanRing`: Turn a Boolean algebra into a Boolean ring.
* `AsBoolAlg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `AsBoolRing`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `BooleanAlgebraOfBooleanRing` and
  `BooleanRingOfBooleanAlgebra`.
* Type-synonyms `AsBoolAlg` and `AsBoolRing`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`ofBoolAlg`/`toBoolAlg`/`ofBoolRing`/`toBoolRing` explicitly.

## Tags

boolean ring, boolean algebra
-/

@[expose] public section

open scoped symmDiff

variable {α β γ : Type*}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class BooleanRing (α) extends Ring α where
  /-- Multiplication in a Boolean ring is idempotent. -/
  isIdempotentElem (a : α) : IsIdempotentElem a

namespace BooleanRing

variable [BooleanRing α] (a b : α)

/--
@isnad1 id=eq.0h2v.s4.6859eb083022 from=seed src=0 shape=ec5be267 vocab=273717c5
-/
@[scoped simp]
lemma mul_self : a * a = a := IsIdempotentElem.eq (isIdempotentElem a)

instance : Std.IdempotentOp (α := α) (· * ·) :=
  ⟨BooleanRing.mul_self⟩

/--
@isnad1 id=eq.0h2v.s5.24f6a9eace8c from=seed src=0 shape=37e9f17c vocab=9df7dbf4
-/
@[scoped simp]
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [right_eq_add] at this

/--
@isnad1 id=eq.0h2v.s4.8ba232521284 from=seed src=0 shape=8d0018bb vocab=2c6c2eba
-/
@[scoped simp]
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self, zero_add]

/--
@isnad1 id=iff.0h3v.s5.2cdf58c53d83 from=seed src=0 shape=c879f03b vocab=9df7dbf4
-/
theorem add_eq_zero' : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]

/--
@isnad1 id=eq.0h3v.s6.e0954ec6f9a6 from=seed src=0 shape=684e9f4d vocab=2403c78d
-/
@[simp]
theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [left_eq_add] at this

/--
@isnad1 id=eq.0h3v.s5.10fd06ca8947 from=seed src=0 shape=b11bd855 vocab=691bea18
-/
@[scoped simp]
theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, neg_eq]

/--
@isnad1 id=eq.0h2v.s6.5fee99c2841d from=seed src=0 shape=92bcfa11 vocab=2403c78d
-/
@[simp]
theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]

-- Note [lower instance priority]
instance (priority := 100) toCommRing : CommRing α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by rw [← add_eq_zero', mul_add_mul] }

end BooleanRing

instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolAlg (α : Type*) :=
  α

/-- The "identity" equivalence between `AsBoolAlg α` and `α`. -/
def toBoolAlg : α ≃ AsBoolAlg α :=
  Equiv.refl _

/-- The "identity" equivalence between `α` and `AsBoolAlg α`. -/
def ofBoolAlg : AsBoolAlg α ≃ α :=
  Equiv.refl _

/--
@isnad1 id=eq.0h1v.s3.e1528e1bd758 from=seed src=0 shape=9d746310 vocab=e1d72a5f
-/
@[simp]
theorem toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.0d9c500ed928 from=seed src=0 shape=e5cab704 vocab=e1d72a5f
-/
@[simp]
theorem ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.f46131b0badb from=seed src=0 shape=6198f7f1 vocab=26f062b8
-/
@[simp]
theorem toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.1e86df0904f8 from=seed src=0 shape=fa7330c4 vocab=26f062b8
-/
@[simp]
theorem ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a :=
  rfl

/--
@isnad1 id=iff.0h3v.s6.6f0d39495eed from=seed src=0 shape=5e10f266 vocab=60d06b5c
-/
theorem toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s6.0a369be26aca from=seed src=0 shape=49fd6368 vocab=ff378794
-/
theorem ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b :=
  Iff.rfl

instance [Inhabited α] : Inhabited (AsBoolAlg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
@[instance_reducible]
def sup : Max α :=
  ⟨fun x y => x + y + x * y⟩

/-- The meet operation in a Boolean ring is `x * y`. -/
@[instance_reducible]
def inf : Min α :=
  ⟨(· * ·)⟩

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup
scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf
open BooleanAlgebraOfBooleanRing

/--
@isnad1 id=eq.0h3v.s4.db8e4277aa01 from=seed src=0 shape=214f988b vocab=3f750906
-/
theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  dsimp only [(· ⊔ ·)]
  ring

/--
@isnad1 id=eq.0h3v.s4.ea85e49345f7 from=seed src=0 shape=214f988b vocab=a6b00818
-/
theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  dsimp only [(· ⊓ ·)]
  ring

/--
@isnad1 id=eq.0h4v.s5.582d0a5be8b4 from=seed src=0 shape=ba6d73b5 vocab=3f750906
-/
theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  dsimp only [(· ⊔ ·)]
  ring

/--
@isnad1 id=eq.0h4v.s5.d4e413929c42 from=seed src=0 shape=ba6d73b5 vocab=a6b00818
-/
theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  dsimp only [(· ⊓ ·)]
  ring

/--
@isnad1 id=eq.0h3v.s4.737ea877018e from=seed src=0 shape=5c53142e vocab=1932c7db
-/
theorem sup_inf_self (a b : α) : a ⊔ a ⊓ b = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [← mul_assoc, mul_self, add_assoc, add_self, add_zero]

/--
@isnad1 id=eq.0h3v.s4.cd33f2efcee6 from=seed src=0 shape=5c53142e vocab=1932c7db
-/
theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add, mul_add, mul_self, ← mul_assoc, mul_self, add_assoc, add_self, add_zero]

/--
@isnad1 id=eq.0h4v.s7.3f6670a0bd1d from=seed src=0 shape=dd255178 vocab=2403c78d
-/
theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) := by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]

/--
@isnad1 id=eq.0h4v.s5.319b33ce3f37 from=seed src=0 shape=af535199 vocab=1932c7db
-/
theorem le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux, add_self, mul_self, zero_add]

/-- The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
@[instance_reducible]
def toBooleanAlgebra : BooleanAlgebra α :=
  { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self with
    le_sup_inf := le_sup_inf
    top := 1
    le_top := fun a => show a + 1 + a * 1 = 1 by rw [mul_one, add_comm a 1,
                                                     add_assoc, add_self, add_zero]
    bot := 0
    bot_le := fun a => show 0 + a + 0 * a = a by rw [zero_mul, zero_add, add_zero]
    compl := fun a => 1 + a
    inf_compl_le_bot := fun a =>
      show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by simp [mul_add, mul_self, add_self]
    top_le_sup_compl := fun a => by
      change
        1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) =
          a + (1 + a) + a * (1 + a)
      simp [mul_add, mul_self, add_self, ← add_assoc 1 a] }

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.toBooleanAlgebra

end BooleanRing

open BooleanRing

instance : BooleanAlgebra (AsBoolAlg α) :=
  fast_instance% @BooleanRing.toBooleanAlgebra α _

/--
@isnad1 id=eq.0h1v.s5.b5db68f63eb2 from=seed src=0 shape=2bb7eda3 vocab=36774377
-/
@[simp]
theorem ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.e1a17cc4f539 from=seed src=0 shape=2bb7eda3 vocab=f44dd6e2
-/
@[simp]
theorem ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.3187f393dc37 from=seed src=0 shape=7be19fe0 vocab=056ac3fd
-/
@[simp]
theorem ofBoolAlg_sup (a b : AsBoolAlg α) :
    ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBoolAlg b + ofBoolAlg a * ofBoolAlg b :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.1b3f84973bd8 from=seed src=0 shape=3e70aa46 vocab=1ec9971c
-/
@[simp]
theorem ofBoolAlg_inf (a b : AsBoolAlg α) : ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBoolAlg b :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.a8da0d787e86 from=seed src=0 shape=b8d8f3af vocab=422bac10
-/
@[simp]
theorem ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.5a681be2cb03 from=seed src=0 shape=264ee5b3 vocab=3bc71acd
-/
@[simp]
theorem ofBoolAlg_sdiff (a b : AsBoolAlg α) : ofBoolAlg (a \ b) = ofBoolAlg a * (1 + ofBoolAlg b) :=
  rfl

private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]

/--
@isnad1 id=eq.0h3v.s7.0760bbbae182 from=seed src=0 shape=3e70aa46 vocab=9b6d45ff
-/
@[simp]
theorem ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (a ∆ b) = ofBoolAlg a + ofBoolAlg b := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symmDiff_aux _ _

/--
@isnad1 id=iff.0h3v.s7.fae953a32084 from=seed src=0 shape=b49fb134 vocab=68b1d9bd
-/
@[simp]
theorem ofBoolAlg_mul_ofBoolAlg_eq_left_iff {a b : AsBoolAlg α} :
    ofBoolAlg a * ofBoolAlg b = ofBoolAlg a ↔ a ≤ b :=
  @inf_eq_left (AsBoolAlg α) _ _ _

/--
@isnad1 id=eq.0h1v.s5.488fa7e423df from=seed src=0 shape=4147bc2f vocab=33fcbd48
-/
@[simp]
theorem toBoolAlg_zero : toBoolAlg (0 : α) = ⊥ :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.62d65b2e3aa6 from=seed src=0 shape=4147bc2f vocab=4341d392
-/
@[simp]
theorem toBoolAlg_one : toBoolAlg (1 : α) = ⊤ :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.00f3ca9feac5 from=seed src=0 shape=3329f06b vocab=8b9c70c9
-/
@[simp]
theorem toBoolAlg_mul (a b : α) : toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.4790c268a6ef from=seed src=0 shape=0bfa4010 vocab=56a0975a
-/
@[simp]
theorem toBoolAlg_add_add_mul (a b : α) : toBoolAlg (a + b + a * b) = toBoolAlg a ⊔ toBoolAlg b :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.3ff7cd9390ea from=seed src=0 shape=3329f06b vocab=01d379cf
-/
@[simp]
theorem toBoolAlg_add (a b : α) : toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b :=
  (ofBoolAlg_symmDiff a b).symm

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
protected def RingHom.asBoolAlg (f : α →+* β) : BoundedLatticeHom (AsBoolAlg α) (AsBoolAlg β) where
  toFun := toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

/--
@isnad1 id=eq.0h1v.s6.d5c0ac699c11 from=seed src=0 shape=a9843297 vocab=f9e3a704
-/
@[simp]
theorem RingHom.asBoolAlg_id : (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _ :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.9c81c826cab0 from=seed src=0 shape=a7146c40 vocab=8d87f5e4
-/
@[simp]
theorem RingHom.asBoolAlg_comp (g : β →+* γ) (f : α →+* β) :
    (g.comp f).asBoolAlg = g.asBoolAlg.comp f.asBoolAlg :=
  rfl

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolRing (α : Type*) :=
  α

/-- The "identity" equivalence between `AsBoolRing α` and `α`. -/
def toBoolRing : α ≃ AsBoolRing α :=
  Equiv.refl _

/-- The "identity" equivalence between `α` and `AsBoolRing α`. -/
def ofBoolRing : AsBoolRing α ≃ α :=
  Equiv.refl _

/--
@isnad1 id=eq.0h1v.s3.e0d2e01f503b from=seed src=0 shape=9d746310 vocab=54873e9b
-/
@[simp]
theorem toBoolRing_symm_eq : (@toBoolRing α).symm = ofBoolRing :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.3491731d4f61 from=seed src=0 shape=e5cab704 vocab=54873e9b
-/
@[simp]
theorem ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.1fce16c75d78 from=seed src=0 shape=6198f7f1 vocab=64516a3c
-/
@[simp]
theorem toBoolRing_ofBoolRing (a : AsBoolRing α) : toBoolRing (ofBoolRing a) = a :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.eafb3b6f7cc9 from=seed src=0 shape=fa7330c4 vocab=64516a3c
-/
@[simp]
theorem ofBoolRing_toBoolRing (a : α) : ofBoolRing (toBoolRing a) = a :=
  rfl

/--
@isnad1 id=iff.0h3v.s6.a2540a9acc68 from=seed src=0 shape=5e10f266 vocab=93364547
-/
theorem toBoolRing_inj {a b : α} : toBoolRing a = toBoolRing b ↔ a = b :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s6.44b1ebd8f502 from=seed src=0 shape=49fd6368 vocab=8891171f
-/
theorem ofBoolRing_inj {a b : AsBoolRing α} : ofBoolRing a = ofBoolRing b ↔ a = b :=
  Iff.rfl

instance [Inhabited α] : Inhabited (AsBoolRing α) :=
  ⟨default (α := α)⟩

-- See note [reducible non-instances]
/-- Every generalized Boolean algebra has the structure of a nonunital commutative ring with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
abbrev GeneralizedBooleanAlgebra.toNonUnitalCommRing [GeneralizedBooleanAlgebra α] :
    NonUnitalCommRing α where
  add := (· ∆ ·)
  add_assoc := symmDiff_assoc
  zero := ⊥
  zero_add := bot_symmDiff
  add_zero := symmDiff_bot
  zero_mul := bot_inf_eq
  mul_zero := inf_bot_eq
  neg := id
  neg_add_cancel := symmDiff_self
  add_comm := symmDiff_comm
  mul := (· ⊓ ·)
  mul_assoc := inf_assoc
  mul_comm := inf_comm
  left_distrib := inf_symmDiff_distrib_left
  right_distrib := inf_symmDiff_distrib_right
  nsmul := letI : Zero α := ⟨⊥⟩; letI : Add α := ⟨(· ∆ ·)⟩; nsmulRec
  zsmul := letI : Zero α := ⟨⊥⟩; letI : Add α := ⟨(· ∆ ·)⟩; letI : Neg α := ⟨id⟩; zsmulRec

instance [GeneralizedBooleanAlgebra α] : NonUnitalCommRing (AsBoolRing α) :=
  @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

-- See note [reducible non-instances]
/-- Every Boolean algebra has the structure of a Boolean ring with the following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
abbrev BooleanAlgebra.toBooleanRing : BooleanRing α where
  __ := GeneralizedBooleanAlgebra.toNonUnitalCommRing
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  isIdempotentElem := inf_idem

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

instance : BooleanRing (AsBoolRing α) :=
  fast_instance% @BooleanAlgebra.toBooleanRing α _

/--
@isnad1 id=eq.0h1v.s5.f72bd0733671 from=seed src=0 shape=96766228 vocab=37856c19
-/
@[simp]
theorem ofBoolRing_zero : ofBoolRing (0 : AsBoolRing α) = ⊥ :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.f90971d15233 from=seed src=0 shape=96766228 vocab=7d58b9cc
-/
@[simp]
theorem ofBoolRing_one : ofBoolRing (1 : AsBoolRing α) = ⊤ :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.57e42a6453c5 from=seed src=0 shape=862f55fc vocab=ecf443fa
-/
@[simp]
theorem ofBoolRing_neg (a : AsBoolRing α) : ofBoolRing (-a) = ofBoolRing a :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.c1dd5d38de32 from=seed src=0 shape=9183dde0 vocab=d131351b
-/
@[simp]
theorem ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.20ceb8375a37 from=seed src=0 shape=9183dde0 vocab=64d784a7
-/
@[simp]
theorem ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.c12f029b9431 from=seed src=0 shape=9183dde0 vocab=0e52b368
-/
@[simp]
theorem ofBoolRing_mul (a b : AsBoolRing α) : ofBoolRing (a * b) = ofBoolRing a ⊓ ofBoolRing b :=
  rfl

/--
@isnad1 id=iff.0h3v.s6.10b439448237 from=seed src=0 shape=f072d4dc vocab=448a839d
-/
@[simp]
theorem ofBoolRing_le_ofBoolRing_iff {a b : AsBoolRing α} :
    ofBoolRing a ≤ ofBoolRing b ↔ a * b = a :=
  inf_eq_left.symm

/--
@isnad1 id=eq.0h1v.s5.00c730dd71d5 from=seed src=0 shape=61a7dfa5 vocab=5d9910f7
-/
@[simp]
theorem toBoolRing_bot : toBoolRing (⊥ : α) = 0 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.9311906bae2a from=seed src=0 shape=61a7dfa5 vocab=2e56c7ec
-/
@[simp]
theorem toBoolRing_top : toBoolRing (⊤ : α) = 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.bffad55b2017 from=seed src=0 shape=8eaaae91 vocab=19cb615c
-/
@[simp]
theorem toBoolRing_inf (a b : α) : toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing b :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.c08c51513c77 from=seed src=0 shape=8eaaae91 vocab=7030c1a7
-/
@[simp]
theorem toBoolRing_symmDiff (a b : α) : toBoolRing (a ∆ b) = toBoolRing a + toBoolRing b :=
  rfl

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps]
protected def BoundedLatticeHom.asBoolRing (f : BoundedLatticeHom α β) :
    AsBoolRing α →+* AsBoolRing β where
  toFun := toBoolRing ∘ f ∘ ofBoolRing
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symmDiff' f
  map_mul' := f.map_inf'

/--
@isnad1 id=eq.0h1v.s6.a0575a7f1bad from=seed src=0 shape=a9843297 vocab=344e11ae
-/
@[simp]
theorem BoundedLatticeHom.asBoolRing_id : (BoundedLatticeHom.id α).asBoolRing = RingHom.id _ :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.09bbecb2ea45 from=seed src=0 shape=afa9d501 vocab=37323cb1
-/
@[simp]
theorem BoundedLatticeHom.asBoolRing_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).asBoolRing = g.asBoolRing.comp f.asBoolRing :=
  rfl

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps!]
def OrderIso.asBoolAlgAsBoolRing (α : Type*) [BooleanAlgebra α] : AsBoolAlg (AsBoolRing α) ≃o α :=
  ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps!]
def RingEquiv.asBoolRingAsBoolAlg (α : Type*) [BooleanRing α] : AsBoolRing (AsBoolAlg α) ≃+* α :=
  { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }

open Bool

instance : Zero Bool where zero := false

instance : One Bool where one := true

instance : Add Bool where add := xor

instance : Neg Bool where neg := id

instance : Sub Bool where sub := xor

instance : Mul Bool where mul := and

instance : BooleanRing Bool where
  add_assoc := xor_assoc
  zero_add := Bool.false_xor
  add_zero := Bool.xor_false
  neg_add_cancel := Bool.xor_self
  add_comm := xor_comm
  mul_assoc := and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := and_xor_distrib_left
  right_distrib := and_xor_distrib_right
  isIdempotentElem := Bool.and_self
  zero_mul _ := rfl
  mul_zero a := by cases a <;> rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/--
@isnad1 id=eq.0h0v.s3.7424501f9b69 from=seed src=0 shape=ff3a10fc vocab=86b9df36
-/
theorem Bool.zero_eq_false : 0 = false := rfl

/--
@isnad1 id=eq.0h0v.s3.4300770f95bb from=seed src=0 shape=ff3a10fc vocab=38cd4b6b
-/
theorem Bool.one_eq_true : 1 = true := rfl

/--
@isnad1 id=eq.0h2v.s4.ec348034955e from=seed src=0 shape=34900cef vocab=5ed7f064
-/
theorem Bool.add_eq_xor (b c : Bool) : b + c = (b ^^ c) := rfl

/--
@isnad1 id=eq.0h1v.s3.c1df69b1e43d from=seed src=0 shape=9023e767 vocab=9c161fa5
-/
theorem Bool.neg_eq_id (b : Bool) : -b = b := rfl

/--
@isnad1 id=eq.0h2v.s4.ae8a64b837aa from=seed src=0 shape=34900cef vocab=25b6323f
-/
theorem Bool.sub_eq_xor (b c : Bool) : b - c = (b ^^ c) := rfl

/--
@isnad1 id=eq.0h2v.s4.0f4cdd9c2850 from=seed src=0 shape=34900cef vocab=cf2aa8d2
-/
theorem Bool.mul_eq_and (b c : Bool) : b * c = (b && c) := rfl
