/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku
public import Tengoku.Imoshortlist.IMOSLLean4.Extra.CharTwo.Ring

/-!
# Explicit construction of `𝔽₂`

In this file, we explicitly construct `𝔽₂`, the field of 2 elements.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₂`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

open Extra

inductive 𝔽₂
  | O : 𝔽₂
  | I : 𝔽₂

namespace 𝔽₂

protected def add : 𝔽₂ → 𝔽₂ → 𝔽₂
  | O, x => x
  | I, O => I
  | I, I => O

protected def mul : 𝔽₂ → 𝔽₂ → 𝔽₂
  | O, _ => O
  | I, x => x

instance : Zero 𝔽₂ := ⟨O⟩
instance : One 𝔽₂ := ⟨I⟩
instance : Add 𝔽₂ := ⟨𝔽₂.add⟩
instance : Neg 𝔽₂ := ⟨id⟩
instance : Mul 𝔽₂ := ⟨𝔽₂.mul⟩

/-! ### `𝔽₂` is a commutative group -/

/--
@isnad1 id=eq.0h1v.s4.108970abe549 from=translated src=- shape=bbd74598 vocab=df4b3b99
-/
protected theorem zero_add (x : 𝔽₂) : 0 + x = x := rfl

/--
@isnad1 id=eq.0h1v.s4.e1d401db9b92 from=translated src=- shape=eeffd242 vocab=df4b3b99
-/
protected theorem add_zero : ∀ x : 𝔽₂, x + 0 = x
  | O => rfl
  | I => rfl

/--
@isnad1 id=eq.0h2v.s4.434f56bbee64 from=translated src=- shape=900bc7c0 vocab=df4b3b99
-/
protected theorem add_comm : ∀ x y : 𝔽₂, x + y = y + x
  | O, O => rfl
  | O, I => rfl
  | I, O => rfl
  | I, I => rfl

/--
@isnad1 id=eq.0h3v.s5.cd492135041d from=translated src=- shape=03a6b791 vocab=df4b3b99
-/
protected theorem add_assoc : ∀ x y z : 𝔽₂, x + y + z = x + (y + z)
  | O, _, _ => rfl
  | I, O, _ => rfl
  | I, I, O => rfl
  | I, I, I => rfl

/--
@isnad1 id=eq.0h1v.s4.18160a98b7a4 from=translated src=- shape=f2c77883 vocab=9a5c2b9b
-/
protected theorem neg_add_cancel : ∀ x : 𝔽₂, -x + x = 0
  | O => rfl
  | I => rfl

instance : AddCommGroup 𝔽₂ :=
  { add_assoc := 𝔽₂.add_assoc
    zero_add := 𝔽₂.zero_add
    add_zero := 𝔽₂.add_zero
    add_comm := 𝔽₂.add_comm
    neg_add_cancel := 𝔽₂.neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-! ### `𝔽₂` is a ring -/

/--
@isnad1 id=eq.0h1v.s4.5537d18c319e from=translated src=- shape=8c4189b2 vocab=56b114ee
-/
protected theorem zero_mul (x : 𝔽₂) : 0 * x = 0 := rfl

/--
@isnad1 id=eq.0h1v.s4.0e3ddc7085e1 from=translated src=- shape=4b31552c vocab=56b114ee
-/
protected theorem mul_zero : ∀ x : 𝔽₂, x * 0 = 0
  | O => rfl
  | I => rfl

/--
@isnad1 id=eq.0h1v.s4.673cdbd482a5 from=translated src=- shape=bbd74598 vocab=56b114ee
-/
protected theorem one_mul (x : 𝔽₂) : 1 * x = x := rfl

/--
@isnad1 id=eq.0h1v.s4.05d5d75e7b77 from=translated src=- shape=eeffd242 vocab=56b114ee
-/
protected theorem mul_one : ∀ x : 𝔽₂, x * 1 = x
  | O => rfl
  | I => rfl

/--
@isnad1 id=eq.0h2v.s4.2166bcdaf5ee from=translated src=- shape=900bc7c0 vocab=56b114ee
-/
protected theorem mul_comm : ∀ x y : 𝔽₂, x * y = y * x
  | O, O => rfl
  | O, I => rfl
  | I, O => rfl
  | I, I => rfl

/--
@isnad1 id=eq.0h3v.s5.06017770761b from=translated src=- shape=03a6b791 vocab=56b114ee
-/
protected theorem mul_assoc : ∀ x y z : 𝔽₂, x * y * z = x * (y * z)
  | O, _, _ => rfl
  | I, _, _ => rfl

/--
@isnad1 id=eq.0h3v.s5.636279bd03e2 from=translated src=- shape=1dfc5842 vocab=feb66db8
-/
protected theorem mul_add : ∀ x y z : 𝔽₂, x * (y + z) = x * y + x * z
  | O, _, _ => rfl
  | I, _, _ => rfl

/--
@isnad1 id=eq.0h3v.s5.a3d845926767 from=translated src=- shape=89e741f9 vocab=feb66db8
-/
protected theorem add_mul : ∀ x y z : 𝔽₂, (x + y) * z = x * z + y * z
  | O, _, _ => rfl
  | I, O, O => rfl
  | I, O, I => rfl
  | I, I, O => rfl
  | I, I, I => rfl

instance : CommRing 𝔽₂ :=
  { 𝔽₂.instAddCommGroup with
    zero_mul := 𝔽₂.zero_mul
    mul_zero := 𝔽₂.mul_zero
    mul_assoc := 𝔽₂.mul_assoc
    one_mul := 𝔽₂.one_mul
    mul_one := 𝔽₂.mul_one
    mul_comm := 𝔽₂.mul_comm
    left_distrib := 𝔽₂.mul_add
    right_distrib := 𝔽₂.add_mul }

/-! ### Ring homomorphism from `𝔽₂` -/

def cast [AddMonoidWithOne R] : 𝔽₂ → R
  | O => 0
  | I => 1

/--
@isnad1 id=eq.0h3v.s5.cf646df0c756 from=translated src=- shape=381327d9 vocab=13a3e76e
-/
theorem cast_mul [NonAssocSemiring R] : ∀ x y : 𝔽₂, cast (R := R) (x * y) = cast x * cast y
  | O, _ => (zero_mul _).symm
  | I, _ => (one_mul _).symm

variable [NonAssocSemiring R] [CharTwo R]
