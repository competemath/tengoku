/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# Explicit construction of `ℤφ`

In this file, we explicitly construct the ring $ℤ[\phi]$,
  denoted `ℤφ`, where $φ = \frac{1 + \sqrt{5}}{2}$.
We prove just the necessary properties for the purpose of the main problem.

TODO:
* Remove the need for `ring` tactic in `ℤφ.mul_assoc` if possible.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

/-- The ring `Z[φ]`, where `φ = (1 + √5)/2`.
  The components are called `re` and `im`, following Mathlib's `Zsqrtd` API. -/
@[ext] structure ℤφ where
  re : ℤ
  im : ℤ

namespace ℤφ

def φ : ℤφ := ⟨0, 1⟩

protected def add : ℤφ → ℤφ → ℤφ
  | ⟨a, b⟩, ⟨a', b'⟩ => ⟨a + a', b + b'⟩

protected def neg : ℤφ → ℤφ
  | ⟨a, b⟩ => ⟨-a, -b⟩

protected def mul : ℤφ → ℤφ → ℤφ
  | ⟨a, b⟩, ⟨a', b'⟩ => ⟨a * a' + b * b', a * b' + a' * b + b * b'⟩

instance : Zero ℤφ := ⟨0, 0⟩
instance : One ℤφ := ⟨1, 0⟩
instance : Add ℤφ := ⟨ℤφ.add⟩
instance : Neg ℤφ := ⟨ℤφ.neg⟩
instance : Mul ℤφ := ⟨ℤφ.mul⟩

/--
@isnad1 id=eq.0h0v.s4.8d417471605a from=translated src=- shape=14c904fa vocab=7b0a7357
-/
lemma zero_def : (0 : ℤφ) = ⟨0, 0⟩ := rfl

/--
@isnad1 id=eq.0h0v.s4.c502069b9e05 from=translated src=- shape=14c904fa vocab=7b0a7357
-/
lemma one_def : (1 : ℤφ) = ⟨1, 0⟩ := rfl

/--
@isnad1 id=eq.0h4v.s5.fcdbf422936b from=translated src=- shape=8a7b2152 vocab=768523cd
-/
lemma add_def (a b a' b' : ℤ) : (⟨a, b⟩ : ℤφ) + ⟨a', b'⟩ = ⟨a + a', b + b'⟩ := rfl

/--
@isnad1 id=eq.0h2v.s4.6a3a2c82eceb from=translated src=- shape=69e66d77 vocab=c930b486
-/
lemma neg_def (a b : ℤ) : -(⟨a, b⟩ : ℤφ) = ⟨-a, -b⟩ := rfl

/--
@isnad1 id=eq.0h4v.s6.e63585aeee2e from=translated src=- shape=ffde77c4 vocab=453fe08f
-/
lemma mul_def (a b a' b' : ℤ) :
    (⟨a, b⟩ : ℤφ) * ⟨a', b'⟩ = ⟨a * a' + b * b', a * b' + a' * b + b * b'⟩ := rfl

/-! ### `ℤ[φ]` is a commutative group -/

/--
@isnad1 id=eq.0h1v.s4.1f7bc2d3ae7b from=translated src=- shape=eeffd242 vocab=e6defd05
-/
protected theorem add_zero : ∀ x : ℤφ, x + 0 = x
  | ⟨a, b⟩ => ℤφ.ext a.add_zero b.add_zero

/--
@isnad1 id=eq.0h1v.s4.bd42bd13c8a3 from=translated src=- shape=bbd74598 vocab=e6defd05
-/
protected theorem zero_add : ∀ x : ℤφ, 0 + x = x
  | ⟨a, b⟩ => ℤφ.ext a.zero_add b.zero_add

/--
@isnad1 id=eq.0h2v.s4.179da68d3d06 from=translated src=- shape=900bc7c0 vocab=e6defd05
-/
protected theorem add_comm : ∀ x y : ℤφ, x + y = y + x
  | ⟨a, b⟩, ⟨a', b'⟩ => ℤφ.ext (a.add_comm a') (b.add_comm b')

/--
@isnad1 id=eq.0h3v.s5.fbfef91b9abe from=translated src=- shape=03a6b791 vocab=e6defd05
-/
protected theorem add_assoc : ∀ x y z : ℤφ, x + y + z = x + (y + z)
  | ⟨a, b⟩, ⟨a', b'⟩, ⟨a'', b''⟩ => ℤφ.ext (a.add_assoc a' a'') (b.add_assoc b' b'')

/--
@isnad1 id=eq.0h1v.s4.daf962a1474d from=translated src=- shape=f2c77883 vocab=ded38de0
-/
protected theorem neg_add_cancel : ∀ x : ℤφ, -x + x = 0
  | ⟨a, b⟩ => ℤφ.ext a.add_left_neg b.add_left_neg

instance : AddCommGroup ℤφ :=
  { add_assoc := ℤφ.add_assoc
    zero_add := ℤφ.zero_add
    add_zero := ℤφ.add_zero
    add_comm := ℤφ.add_comm
    neg_add_cancel := ℤφ.neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-! ### `ℤ[φ]` is a ring -/

/--
@isnad1 id=eq.0h2v.s4.910a9d9a13e8 from=translated src=- shape=900bc7c0 vocab=a15801b8
-/
protected theorem mul_comm : ∀ x y : ℤφ, x * y = y * x
  | ⟨a, b⟩, ⟨a', b'⟩ => by
      rw [mul_def, mul_def, mul_comm a, mul_comm b, add_comm (a * b')]

/--
@isnad1 id=eq.0h3v.s5.449281901034 from=translated src=- shape=03a6b791 vocab=a15801b8
-/
protected theorem mul_assoc : ∀ x y z : ℤφ, x * y * z = x * (y * z)
  | ⟨a, b⟩, ⟨a', b'⟩, ⟨a'', b''⟩ => by
      rw [mul_def, mul_def, mul_def, mul_def, ℤφ.mk.injEq]
      dsimp only; constructor <;> ring

/--
@isnad1 id=eq.0h1v.s4.4fc740e703e5 from=translated src=- shape=8c4189b2 vocab=a15801b8
-/
protected theorem zero_mul : ∀ x : ℤφ, 0 * x = 0
  | ⟨a, b⟩ => by rw [mul_def, zero_def, zero_mul,
      zero_mul, mul_zero, add_zero, add_zero]

/--
@isnad1 id=eq.0h1v.s4.cce6e83234c5 from=translated src=- shape=4b31552c vocab=a15801b8
-/
protected theorem mul_zero (x : ℤφ) : x * 0 = 0 :=
  (x.mul_comm 0).trans x.zero_mul

/--
@isnad1 id=eq.0h1v.s4.b6701483e116 from=translated src=- shape=bbd74598 vocab=a15801b8
-/
protected theorem one_mul : ∀ x : ℤφ, 1 * x = x
  | ⟨a, b⟩ => by rw [mul_def, one_def, one_mul, one_mul,
      zero_mul, mul_zero, add_zero, add_zero, add_zero]

/--
@isnad1 id=eq.0h1v.s4.b4cf239ea5cf from=translated src=- shape=eeffd242 vocab=a15801b8
-/
protected theorem mul_one (x : ℤφ) : x * 1 = x :=
  (x.mul_comm 1).trans x.one_mul

/--
@isnad1 id=eq.0h3v.s5.0ef7e75b473f from=translated src=- shape=1dfc5842 vocab=8b391aae
-/
protected theorem mul_add : ∀ x y z : ℤφ, x * (y + z) = x * y + x * z
  | ⟨a, b⟩, ⟨a', b'⟩, ⟨a'', b''⟩ => by
      rw [mul_def, mul_def, mul_def, add_def, add_def, ℤφ.mk.injEq]
      dsimp only; constructor
      · rw [add_add_add_comm, ← mul_add, ← mul_add]
      · rw [add_add_add_comm, ← mul_add, add_add_add_comm, ← mul_add, ← add_mul]

/--
@isnad1 id=eq.0h3v.s5.37d9b681926e from=translated src=- shape=89e741f9 vocab=8b391aae
-/
protected theorem add_mul (x y z : ℤφ) : (x + y) * z = x * z + y * z := by
  rw [ℤφ.mul_comm, ℤφ.mul_add, z.mul_comm, z.mul_comm]

instance : CommRing ℤφ :=
  { ℤφ.instAddCommGroup with
    zero_mul := ℤφ.zero_mul
    mul_zero := ℤφ.mul_zero
    mul_assoc := ℤφ.mul_assoc
    one_mul := ℤφ.one_mul
    mul_one := ℤφ.mul_one
    mul_comm := ℤφ.mul_comm
    left_distrib := ℤφ.mul_add
    right_distrib := ℤφ.add_mul }

/-! ### Ring homomorphism from `ℤ[φ]` -/

def cast [AddGroupWithOne R] (r : R) : ℤφ → R
  | ⟨a, b⟩ => a + b • r

/--
@isnad1 id=eq.0h2v.s5.68d7e19bceb5 from=translated src=- shape=4e114734 vocab=7eaf5b57
-/
theorem cast_zero [AddGroupWithOne R] (r : R) : cast r 0 = 0 := by
  change ((0 : ℤ) : R) + 0 • r = 0; rw [Int.cast_zero, zero_add, zero_zsmul]

/--
@isnad1 id=eq.0h2v.s4.e1fa09b5afcc from=translated src=- shape=4e114734 vocab=7eaf5b57
-/
theorem cast_one [AddGroupWithOne R] (r : R) : cast r 1 = 1 := by
  change ((1 : ℤ) : R) + 0 • r = 1; rw [Int.cast_one, zero_zsmul, add_zero]

/--
@isnad1 id=eq.0h2v.s3.dd7bd928d784 from=translated src=- shape=fe003610 vocab=4eb0e414
-/
theorem cast_φ [AddGroupWithOne R] (r : R) : cast r φ = r := by
  change ((0 : ℤ) : R) + 1 • r = r; rw [Int.cast_zero, zero_add, one_zsmul]

/--
@isnad1 id=eq.0h4v.s5.754539dc1d50 from=translated src=- shape=8887f7f7 vocab=ead10157
-/
theorem cast_add [AddCommGroupWithOne R] (r : R) :
    ∀ x y : ℤφ, cast r (x + y) = cast r x + cast r y
  | ⟨a, b⟩, ⟨a', b'⟩ => by
      change ((a + a' : ℤ) : R) + (b + b') • r = _
      rw [Int.cast_add, add_zsmul, add_add_add_comm]; rfl

variable [Ring R] {r : R} (h : r * r = r + 1)
include h

/--
@isnad1 id=eq.1h4v.s6.2b9cbc0b72ca from=translated src=- shape=3cd2684f vocab=969defaa
-/
theorem cast_mul : ∀ x y : ℤφ, cast r (x * y) = cast r x * cast r y
  | ⟨a, b⟩, ⟨a', b'⟩ => by
      change ↑(a * a' + b * b') + (a * b' + a' * b + b * b') • r
        = (↑a + b • r) * (↑a' + b' • r)
      rw [add_zsmul, Int.cast_add, add_add_add_comm, ← zsmul_one (b * b'),
        ← zsmul_add, add_comm 1 r, ← h, add_zsmul, ← add_assoc, mul_zsmul,
        zsmul_eq_mul, Int.cast_mul, ← mul_add, add_mul, add_assoc, add_right_inj,
        mul_add, ← zsmul_eq_mul', mul_zsmul, add_right_inj, mul_zsmul, zsmul_eq_mul,
        zsmul_eq_mul', zsmul_eq_mul, zsmul_eq_mul', mul_assoc, ← mul_assoc]

def castRingHom : ℤφ →+* R :=
  { toFun := cast r
    map_one' := cast_one r
    map_mul' := cast_mul h
    map_zero' := cast_zero r
    map_add' := cast_add r }
