/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# Explicit construction of `𝔽₄`

In this file, we explicitly construct `𝔽₄`, the field of 4 elements.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₄`.

Note that `𝔽₄` can also be obtained as `QuadraticAlgebra (ZMod 2) 1 1`.
However, this very direct implementation has an advantage of faster computations.
-/

@[expose] public section

namespace IMOSL
namespace Extra

open Extra

inductive 𝔽₄
  | O : 𝔽₄
  | I : 𝔽₄
  | X : 𝔽₄
  | Y : 𝔽₄

namespace 𝔽₄

protected def add : 𝔽₄ → 𝔽₄ → 𝔽₄
  | O, x => x
  | x, O => x
  | I, I => O
  | I, X => Y
  | I, Y => X
  | X, I => Y
  | X, X => O
  | X, Y => I
  | Y, I => X
  | Y, X => I
  | Y, Y => O

protected def mul : 𝔽₄ → 𝔽₄ → 𝔽₄
  | O, _ => O
  | I, x => x
  | _, O => O
  | x, I => x
  | X, X => Y
  | X, Y => I
  | Y, X => I
  | Y, Y => X

protected def inv : 𝔽₄ → 𝔽₄
  | O => O
  | I => I
  | X => Y
  | Y => X

protected def div : 𝔽₄ → 𝔽₄ → 𝔽₄
  | _, O => O
  | x, I => x
  | O, _ => O
  | I, X => Y
  | I, Y => X
  | X, X => I
  | X, Y => Y
  | Y, X => X
  | Y, Y => I

instance : Zero 𝔽₄ := ⟨O⟩
instance : One 𝔽₄ := ⟨I⟩
instance : Add 𝔽₄ := ⟨𝔽₄.add⟩
instance : Neg 𝔽₄ := ⟨id⟩
instance : Sub 𝔽₄ := ⟨𝔽₄.add⟩
instance : Mul 𝔽₄ := ⟨𝔽₄.mul⟩
instance : Inv 𝔽₄ := ⟨𝔽₄.inv⟩
instance : Div 𝔽₄ := ⟨𝔽₄.div⟩

instance : DecidableEq 𝔽₄
  | O, O => isTrue rfl
  | O, I => isFalse 𝔽₄.noConfusion
  | O, X => isFalse 𝔽₄.noConfusion
  | O, Y => isFalse 𝔽₄.noConfusion
  | I, O => isFalse 𝔽₄.noConfusion
  | I, I => isTrue rfl
  | I, X => isFalse 𝔽₄.noConfusion
  | I, Y => isFalse 𝔽₄.noConfusion
  | X, O => isFalse 𝔽₄.noConfusion
  | X, I => isFalse 𝔽₄.noConfusion
  | X, X => isTrue rfl
  | X, Y => isFalse 𝔽₄.noConfusion
  | Y, O => isFalse 𝔽₄.noConfusion
  | Y, I => isFalse 𝔽₄.noConfusion
  | Y, X => isFalse 𝔽₄.noConfusion
  | Y, Y => isTrue rfl

/-! ### `𝔽₄` is a commutative group -/

/--
@isnad1 id=eq.0h1v.s4.e6609527dbc8 from=translated src=- shape=eeffd242 vocab=dc99bdf1
-/
protected theorem add_zero : ∀ x : 𝔽₄, x + 0 = x
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

/--
@isnad1 id=eq.0h1v.s4.24924a93c65f from=translated src=- shape=bbd74598 vocab=dc99bdf1
-/
protected theorem zero_add (x : 𝔽₄) : 0 + x = x := rfl

/--
@isnad1 id=eq.0h2v.s4.7c2e9811595a from=translated src=- shape=900bc7c0 vocab=dc99bdf1
-/
protected theorem add_comm : ∀ x y : 𝔽₄, x + y = y + x
  | O, x => x.add_zero.symm
  | x, O => x.add_zero
  | I, I => rfl
  | I, X => rfl
  | I, Y => rfl
  | X, I => rfl
  | X, X => rfl
  | X, Y => rfl
  | Y, I => rfl
  | Y, X => rfl
  | Y, Y => rfl

/--
@isnad1 id=eq.0h3v.s5.625c72f211df from=translated src=- shape=03a6b791 vocab=dc99bdf1
-/
protected theorem add_assoc : ∀ x y z : 𝔽₄, x + y + z = x + (y + z)
  | O, _, _ => rfl
  | x, O, z => congr_arg (· + z) x.add_zero
  | x, y, O => y.add_zero.symm ▸ (x + y).add_zero
  | I, I, I => rfl
  | I, I, X => rfl
  | I, I, Y => rfl
  | I, X, I => rfl
  | I, X, X => rfl
  | I, X, Y => rfl
  | I, Y, I => rfl
  | I, Y, X => rfl
  | I, Y, Y => rfl
  | X, I, I => rfl
  | X, I, X => rfl
  | X, I, Y => rfl
  | X, X, I => rfl
  | X, X, X => rfl
  | X, X, Y => rfl
  | X, Y, I => rfl
  | X, Y, X => rfl
  | X, Y, Y => rfl
  | Y, I, I => rfl
  | Y, I, X => rfl
  | Y, I, Y => rfl
  | Y, X, I => rfl
  | Y, X, X => rfl
  | Y, X, Y => rfl
  | Y, Y, I => rfl
  | Y, Y, X => rfl
  | Y, Y, Y => rfl

/--
@isnad1 id=eq.0h1v.s4.51086a54c8c1 from=translated src=- shape=1347b6cc vocab=dc99bdf1
-/
protected theorem add_self : ∀ x : 𝔽₄, x + x = 0
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

/--
@isnad1 id=eq.0h1v.s3.93b346a8d221 from=translated src=- shape=9023e767 vocab=c33fa9f9
-/
protected theorem neg_def (x : 𝔽₄) : -x = x := rfl

/--
@isnad1 id=eq.0h2v.s4.360aa868fa92 from=translated src=- shape=2c0c907a vocab=144e8283
-/
protected theorem sub_def (x y : 𝔽₄) : x - y = x + y := rfl

/--
@isnad1 id=eq.0h1v.s4.fb971a59c245 from=translated src=- shape=f2c77883 vocab=8711f96d
-/
protected theorem neg_add_cancel (x : 𝔽₄) : -x + x = 0 := by
  rw [𝔽₄.neg_def, 𝔽₄.add_self]

instance : AddCommGroup 𝔽₄ :=
  { add_assoc := 𝔽₄.add_assoc
    zero_add := 𝔽₄.zero_add
    add_zero := 𝔽₄.add_zero
    add_comm := 𝔽₄.add_comm
    neg_add_cancel := 𝔽₄.neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-! ### `𝔽₄` is a ring -/

/--
@isnad1 id=eq.0h1v.s4.a08fe1a10f52 from=translated src=- shape=8c4189b2 vocab=062cb466
-/
protected theorem zero_mul (x : 𝔽₄) : 0 * x = 0 := rfl

/--
@isnad1 id=eq.0h1v.s4.7ba63c556c89 from=translated src=- shape=4b31552c vocab=062cb466
-/
protected theorem mul_zero : ∀ x : 𝔽₄, x * 0 = 0
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

/--
@isnad1 id=eq.0h1v.s4.124b0ab40ea7 from=translated src=- shape=eeffd242 vocab=062cb466
-/
protected theorem mul_one : ∀ x : 𝔽₄, x * 1 = x
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

/--
@isnad1 id=eq.0h1v.s4.271d25e404d9 from=translated src=- shape=bbd74598 vocab=062cb466
-/
protected theorem one_mul (x : 𝔽₄) : 1 * x = x := rfl

/--
@isnad1 id=eq.0h2v.s4.b274238d61f0 from=translated src=- shape=900bc7c0 vocab=062cb466
-/
protected theorem mul_comm : ∀ x y : 𝔽₄, x * y = y * x
  | I, x => x.mul_one.symm
  | x, I => x.mul_one
  | O, O => rfl
  | O, X => rfl
  | O, Y => rfl
  | X, O => rfl
  | X, X => rfl
  | X, Y => rfl
  | Y, O => rfl
  | Y, X => rfl
  | Y, Y => rfl

/--
@isnad1 id=eq.0h3v.s5.aa0db8df5bdc from=translated src=- shape=03a6b791 vocab=062cb466
-/
protected theorem mul_assoc : ∀ x y z : 𝔽₄, x * y * z = x * (y * z)
  | O, _, _ => rfl
  | I, _, _ => rfl
  | X, O, _ => rfl
  | X, I, _ => rfl
  | Y, O, _ => rfl
  | Y, I, _ => rfl
  | X, X, O => rfl
  | X, X, I => rfl
  | X, X, X => rfl
  | X, X, Y => rfl
  | X, Y, O => rfl
  | X, Y, I => rfl
  | X, Y, X => rfl
  | X, Y, Y => rfl
  | Y, X, O => rfl
  | Y, X, I => rfl
  | Y, X, X => rfl
  | Y, X, Y => rfl
  | Y, Y, O => rfl
  | Y, Y, I => rfl
  | Y, Y, X => rfl
  | Y, Y, Y => rfl

/--
@isnad1 id=eq.0h3v.s5.450cb798f387 from=translated src=- shape=1dfc5842 vocab=79ad9d5a
-/
protected theorem mul_add : ∀ x y z : 𝔽₄, x * (y + z) = x * y + x * z
  | O, _, _ => rfl
  | I, _, _ => rfl
  | X, O, _ => rfl
  | X, I, O => rfl
  | X, I, I => rfl
  | X, I, X => rfl
  | X, I, Y => rfl
  | X, X, O => rfl
  | X, X, I => rfl
  | X, X, X => rfl
  | X, X, Y => rfl
  | X, Y, O => rfl
  | X, Y, I => rfl
  | X, Y, X => rfl
  | X, Y, Y => rfl
  | Y, O, _ => rfl
  | Y, I, O => rfl
  | Y, I, I => rfl
  | Y, I, X => rfl
  | Y, I, Y => rfl
  | Y, X, O => rfl
  | Y, X, I => rfl
  | Y, X, X => rfl
  | Y, X, Y => rfl
  | Y, Y, O => rfl
  | Y, Y, I => rfl
  | Y, Y, X => rfl
  | Y, Y, Y => rfl

/--
@isnad1 id=eq.0h3v.s5.cc8f35e8c366 from=translated src=- shape=89e741f9 vocab=79ad9d5a
-/
protected theorem add_mul (x y z : 𝔽₄) : (x + y) * z = x * z + y * z :=
  by rw [𝔽₄.mul_comm, 𝔽₄.mul_add, z.mul_comm, z.mul_comm]

instance : CommRing 𝔽₄ :=
  { 𝔽₄.instAddCommGroup with
    zero_mul := 𝔽₄.zero_mul
    mul_zero := 𝔽₄.mul_zero
    mul_assoc := 𝔽₄.mul_assoc
    one_mul := 𝔽₄.one_mul
    mul_one := 𝔽₄.mul_one
    mul_comm := 𝔽₄.mul_comm
    left_distrib := 𝔽₄.mul_add
    right_distrib := 𝔽₄.add_mul }

/-! ### Some basic arithmetic properties of `𝔽₄` -/

/-- Over `𝔽₄`, we have `0 ≠ 1`.
@isnad1 id=ne.0h0v.s3.c454f4032f24 from=translated src=- shape=91ed63c4 vocab=5d839110
-/
theorem zero_ne_one : (0 : 𝔽₄) ≠ 1 := by decide

/-- We have `X^3 = 1`.
@isnad1 id=eq.0h0v.s5.2bdb113321cd from=translated src=- shape=f9867af3 vocab=2aeaeef8
-/
theorem X_pow_three_eq_one : X ^ 3 = 1 := rfl

/-- We have `Y^3 = 1`.
@isnad1 id=eq.0h0v.s5.52071545759a from=translated src=- shape=f9867af3 vocab=f01cd24c
-/
theorem Y_pow_three_eq_one : Y ^ 3 = 1 := rfl

/-- For any `k : ℕ`, we have `X^k = X^{k % 3}`.
@isnad1 id=eq.0h1v.s5.abb904fc730f from=translated src=- shape=0c3ff7bd vocab=1064a1f1
-/
theorem X_pow_eq_X_pow_mod_three (k : ℕ) : X ^ k = X ^ (k % 3) :=
  calc X ^ k
  _ = X ^ (3 * (k / 3) + k % 3) := by rw [Nat.div_add_mod]
  _ = X ^ (k % 3) := by rw [pow_add, pow_mul, X_pow_three_eq_one, one_pow, 𝔽₄.one_mul]

/-- For any `k : ℕ`, we have `Y^k = Y^{k % 3}`.
@isnad1 id=eq.0h1v.s5.83f6210cb74e from=translated src=- shape=0c3ff7bd vocab=7a1f42e4
-/
theorem Y_pow_eq_Y_pow_mod_three (k : ℕ) : Y ^ k = Y ^ (k % 3) := by
  calc Y ^ k
  _ = Y ^ (3 * (k / 3) + k % 3) := by rw [Nat.div_add_mod]
  _ = Y ^ (k % 3) := by rw [pow_add, pow_mul, Y_pow_three_eq_one, one_pow, 𝔽₄.one_mul]

open Fin.NatCast in
/-- For any `k : ℕ`, we have `X^k + Y^k = 0` if and only if `3 ∣ k`.
@isnad1 id=eq.0h1v.s6.6cffe3a0b86e from=translated src=- shape=9efdacee vocab=040c6d90
-/
theorem X_pow_add_Y_pow (k : ℕ) : X ^ k + Y ^ k = if 3 ∣ k then 0 else 1 :=
  calc X ^ k + Y ^ k
  _ = X ^ ((k : Fin 3).val) + Y ^ ((k : Fin 3).val) :=
    congrArg₂ (· + ·) (X_pow_eq_X_pow_mod_three k) (Y_pow_eq_Y_pow_mod_three k)
  _ = if (k : Fin 3).val = 0 then 0 else 1 :=
    match (k : Fin 3) with | 0 => rfl | 1 => rfl | 2 => rfl
  _ = if 3 ∣ k then 0 else 1 := if_congr Nat.dvd_iff_mod_eq_zero.symm rfl rfl

/-- For any `k : ℕ`, `X^k + Y^k` equals `0` if `3 ∣ k` and `1` otherwise.
@isnad1 id=iff.0h1v.s6.ac9a70da51b8 from=translated src=- shape=2ebbd57e vocab=3c80d929
-/
theorem X_pow_add_Y_pow_eq_zero_iff {k : ℕ} : X ^ k + Y ^ k = 0 ↔ 3 ∣ k := by
  rw [X_pow_add_Y_pow, zero_ne_one.ite_eq_left_iff]
