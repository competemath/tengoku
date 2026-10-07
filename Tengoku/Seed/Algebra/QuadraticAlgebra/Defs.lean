/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Kenny Lau, Jiayang Hong
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
public import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Basic


/-!

# Quadratic Algebra

In this file we define the quadratic algebra `QuadraticAlgebra R a b` over a commutative ring `R`,
and define some algebraic structures on it.

## Main definitions

* `QuadraticAlgebra R a b`:
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b` in `R`.

## Tags

Quadratic algebra, quadratic extension

-/

@[expose] public section

universe u

/-- Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, implemented as
a structure with two fields, `re` and `im`. When `R` is a commutative ring, this is isomorphic to
`R[X]/(X^2-b*X-a)`. -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- Real part of an element in quadratic algebra -/
  re : R
  /-- Imaginary part of an element in quadratic algebra -/
  im : R
deriving DecidableEq

initialize_simps_projections QuadraticAlgebra (as_prefix re, as_prefix im)

variable {R : Type*}
namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps symm_apply]
def equivProd (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

/--
@isnad1 id=eq.0h4v.s4.13ae65079c7b from=seed src=0 shape=74d36278 vocab=5f8284c2
-/
@[simp]
theorem mk_eta {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivProd a b).subsingleton

instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivProd a b).nontrivial

section Zero
variable [Zero R]

/-- The natural function `R → QuadraticAlgebra R a b`.

Note that, if `R` is a ring, you should use `algebraMap` instead of `C`. -/
protected def C (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

/--
@isnad1 id=eq.0h4v.s4.3e9a8766f34e from=seed src=0 shape=4112da5f vocab=d57f9dcc
-/
@[simp]
theorem re_C : (.C r : QuadraticAlgebra R a b).re = r := rfl

/--
@isnad1 id=eq.0h4v.s4.b99ad7d2a0bd from=seed src=0 shape=28f31536 vocab=00f2b55b
-/
@[simp]
theorem im_C : (.C r : QuadraticAlgebra R a b).im = 0 := rfl

/--
@isnad1 id=injectiv.0h3v.s4.3b074833a5c9 from=seed src=0 shape=3b260837 vocab=6cf7adef
-/
theorem C_injective : Function.Injective (.C : R → QuadraticAlgebra R a b) :=
  fun _ _ h => congr_arg re h

/--
@isnad1 id=iff.0h5v.s5.9742a90fe8cb from=seed src=0 shape=ed499359 vocab=d965b04e
-/
@[simp]
theorem C_inj {x y : R} : (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y :=
  C_injective.eq_iff

instance : Zero (QuadraticAlgebra R a b) := ⟨⟨0, 0⟩⟩

/--
@isnad1 id=eq.0h3v.s5.a53a1bc73c15 from=seed src=0 shape=122f25fd vocab=a704d983
-/
@[simp] theorem re_zero : (0 : QuadraticAlgebra R a b).re = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.c6c3961b2679 from=seed src=0 shape=122f25fd vocab=a4a0115d
-/
@[simp] theorem im_zero : (0 : QuadraticAlgebra R a b).im = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.20194ad1eab6 from=seed src=0 shape=2e0f905e vocab=d965b04e
-/
@[simp]
theorem C_zero : (.C 0 : QuadraticAlgebra R a b) = 0 := rfl

/--
@isnad1 id=iff.0h4v.s5.1292002c4a29 from=seed src=0 shape=f3e1a69b vocab=d965b04e
-/
@[simp]
theorem C_eq_zero_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0 := by
  rw [← C_zero, C_inj]

instance : Inhabited (QuadraticAlgebra R a b) := ⟨0⟩

section One
variable [One R]

instance : One (QuadraticAlgebra R a b) := ⟨⟨1, 0⟩⟩

/--
@isnad1 id=eq.0h3v.s5.cef3869f015b from=seed src=0 shape=ece7bb16 vocab=54a77037
-/
@[scoped simp] theorem re_one : (1 : QuadraticAlgebra R a b).re = 1 := rfl

/--
@isnad1 id=eq.0h3v.s5.b0165922ef76 from=seed src=0 shape=ece7bb16 vocab=3d1dbe43
-/
@[scoped simp] theorem im_one : (1 : QuadraticAlgebra R a b).im = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.91540187e2d6 from=seed src=0 shape=dc256092 vocab=bc82fad6
-/
@[simp]
theorem C_one : (.C 1 : QuadraticAlgebra R a b) = 1 := rfl

/--
@isnad1 id=iff.0h4v.s5.266eb59055b0 from=seed src=0 shape=bb0807b3 vocab=bc82fad6
-/
@[simp]
theorem C_eq_one_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1 := by
  rw [← C_one, C_inj]

end One

end Zero

section Add
variable [Add R]

instance : Add (QuadraticAlgebra R a b) where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

/--
@isnad1 id=eq.0h5v.s6.0db3de024c1e from=seed src=0 shape=6d94a147 vocab=65113c3a
-/
@[simp] theorem re_add (z w : QuadraticAlgebra R a b) :
    (z + w).re = z.re + w.re := rfl

/--
@isnad1 id=eq.0h5v.s6.54563b20ad3a from=seed src=0 shape=6d94a147 vocab=c441acf9
-/
@[simp] theorem im_add (z w : QuadraticAlgebra R a b) :
    (z + w).im = z.im + w.im := rfl

/--
@isnad1 id=eq.0h5v.s6.f1897ba224ac from=seed src=0 shape=7b2f41c7 vocab=2a680823
-/
@[simp]
theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    mk z.re z.im + mk w.re w.im = (mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

/--
@isnad1 id=eq.0h5v.s6.5616d0e5ebc9 from=seed src=0 shape=f89843d6 vocab=2b5f132a
-/
@[simp]
theorem C_add (x y : R) : (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y := by
  ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

instance : Neg (QuadraticAlgebra R a b) where neg z := ⟨-z.re, -z.im⟩

/--
@isnad1 id=eq.0h4v.s5.1dbb1a42a33b from=seed src=0 shape=345d0dc8 vocab=0e06ec3f
-/
@[simp] theorem re_neg (z : QuadraticAlgebra R a b) : (-z).re = -z.re := rfl

/--
@isnad1 id=eq.0h4v.s5.8d65171b9a26 from=seed src=0 shape=345d0dc8 vocab=b58dd5b0
-/
@[simp] theorem im_neg (z : QuadraticAlgebra R a b) : (-z).im = -z.im := rfl

/--
@isnad1 id=eq.0h5v.s5.3e13bda83a34 from=seed src=0 shape=690e0645 vocab=bc3adae3
-/
@[simp]
theorem neg_mk (x y : R) :
    -(mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

end Neg

section AddGroup

/--
@isnad1 id=eq.0h4v.s5.0866d36e6a07 from=seed src=0 shape=eb69ab23 vocab=a5302609
-/
@[simp]
theorem C_neg [NegZeroClass R] (x : R) : (.C (-x) : QuadraticAlgebra R a b) = -.C x := by
  ext <;> simp

instance [Sub R] : Sub (QuadraticAlgebra R a b) where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩

/--
@isnad1 id=eq.0h5v.s6.02517b1a80db from=seed src=0 shape=6d94a147 vocab=d7b2f6cc
-/
@[simp] theorem re_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).re = z.re - w.re := rfl

/--
@isnad1 id=eq.0h5v.s6.07b174d8e046 from=seed src=0 shape=6d94a147 vocab=993640b6
-/
@[simp] theorem im_sub [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).im = z.im - w.im := rfl

/--
@isnad1 id=eq.0h7v.s6.256dac50a21f from=seed src=0 shape=bd6e21c0 vocab=6f26877d
-/
@[simp]
theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) - mk x2 y2 = mk (x1 - x2) (y1 - y2) := rfl

/--
@isnad1 id=eq.0h5v.s6.b947bb2ea3e4 from=seed src=0 shape=8e592eeb vocab=3219fba7
-/
@[simp]
theorem C_sub (r1 r2 : R) [SubNegZeroMonoid R] :
    (.C (r1 - r2) : QuadraticAlgebra R a b) = .C r1 - .C r2 :=
  QuadraticAlgebra.ext rfl zero_sub_zero.symm

end AddGroup

section Mul
variable [Mul R] [Add R]

instance : Mul (QuadraticAlgebra R a b) where
  mul z w := ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩

/--
@isnad1 id=eq.0h5v.s6.23f12ae804dd from=seed src=0 shape=3626e36d vocab=aa36e59d
-/
@[simp] theorem re_mul (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + a * z.im * w.im := rfl

/--
@isnad1 id=eq.0h5v.s6.3e24757888c8 from=seed src=0 shape=283cb21f vocab=aa36e59d
-/
@[simp] theorem im_mul (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im := rfl

/--
@isnad1 id=eq.0h7v.s7.9e343c4188ae from=seed src=0 shape=235f8d33 vocab=0b00713a
-/
@[simp]
theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 y2 =
    mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2) := rfl

end Mul

section SMul
variable [SMul S R] [SMul T R] (s : S)

instance : SMul S (QuadraticAlgebra R a b) where smul s z := ⟨s • z.re, s • z.im⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  smul_assoc s t z := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  smul_comm s t z := by ext <;> exact smul_comm _ _ _

instance [SMul Sᵐᵒᵖ R] [IsCentralScalar S R] : IsCentralScalar S (QuadraticAlgebra R a b) where
  op_smul_eq_smul s z := by ext <;> exact op_smul_eq_smul _ _

/--
@isnad1 id=eq.0h6v.s5.d2a5c5f62f71 from=seed src=0 shape=3888449a vocab=ce38d8ef
-/
@[simp] theorem re_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).re = s • z.re := rfl

/--
@isnad1 id=eq.0h6v.s5.d2ac2f66101b from=seed src=0 shape=3888449a vocab=a909c24b
-/
@[simp] theorem im_smul (s : S) (z : QuadraticAlgebra R a b) : (s • z).im = s • z.im := rfl

/--
@isnad1 id=eq.0h7v.s6.392210b58b73 from=seed src=0 shape=755c0d6a vocab=a74029d7
-/
@[simp]
theorem smul_mk (s : S) (x y : R) :
    s • (mk x y : QuadraticAlgebra R a b) = mk (s • x) (s • y) := rfl

end SMul

section MulAction

instance [Monoid S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

end MulAction

/--
@isnad1 id=eq.0h6v.s6.4293e59f5428 from=seed src=0 shape=eccc6398 vocab=9c0df7c4
-/
@[simp]
theorem C_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (.C (s • r) : QuadraticAlgebra R a b) = s • .C r :=
  QuadraticAlgebra.ext rfl (smul_zero _).symm

instance [AddMonoid R] : AddMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] :
    DistribMulAction S (QuadraticAlgebra R a b) where
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

instance [AddCommMonoid R] : AddCommMonoid (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addCommMonoid _ rfl ?_ ?_ <;> intros <;> rfl

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  add_smul r s x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

instance [AddGroup R] : AddGroup (QuadraticAlgebra R a b) := fast_instance% by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

instance [AddCommGroup R] : AddCommGroup (QuadraticAlgebra R a b) where

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

instance : AddCommMonoidWithOne (QuadraticAlgebra R a b) where
  natCast n := .C n
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

/--
@isnad1 id=eq.0h4v.s6.0fdbdd6d1243 from=seed src=0 shape=07b0aa11 vocab=3be330f9
-/
@[simp]
theorem C_ofNat (n : ℕ) [n.AtLeastTwo] :
    (.C (ofNat(n) : R) : QuadraticAlgebra R a b) = ofNat(n) := by
  ext <;> rfl

/--
@isnad1 id=eq.0h4v.s5.667cdef01aef from=seed src=0 shape=4542827b vocab=3ee71cbb
-/
@[simp, norm_cast]
theorem re_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).re = n := rfl

/--
@isnad1 id=eq.0h4v.s5.b5b1040aff0e from=seed src=0 shape=76d57f3e vocab=e42b322e
-/
@[simp, norm_cast]
theorem im_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

/--
@isnad1 id=eq.0h4v.s5.4f3392a92fe5 from=seed src=0 shape=6e824ed0 vocab=4dc96768
-/
theorem C_natCast (n : ℕ) : .C (n : R) = (↑n : QuadraticAlgebra R a b) := rfl

/--
@isnad1 id=eq.0h4v.s5.1e2ac04a7e70 from=seed src=0 shape=e9f775e5 vocab=2420753d
-/
@[scoped simp]
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

/--
@isnad1 id=eq.0h4v.s6.6d5b4cdab80b from=seed src=0 shape=23229dee vocab=09b78d8b
-/
@[scoped simp]
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

end AddCommMonoidWithOne

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne (QuadraticAlgebra R a b) where
  intCast n := .C n
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, C_neg]; norm_cast

/--
@isnad1 id=eq.0h4v.s5.7782d5806150 from=seed src=0 shape=4542827b vocab=c7922a8b
-/
@[simp, norm_cast]
theorem re_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).re = n := rfl

/--
@isnad1 id=eq.0h4v.s5.667b5237b1e2 from=seed src=0 shape=76d57f3e vocab=1a8f2e8a
-/
@[simp, norm_cast]
theorem im_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

/--
@isnad1 id=eq.0h4v.s5.956ffa5be7cb from=seed src=0 shape=6e824ed0 vocab=e819845b
-/
theorem C_intCast (n : ℤ) : .C (n : R) = (n : QuadraticAlgebra R a b) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (QuadraticAlgebra R a b) where
  left_distrib _ _ _ := by ext <;> simp [mul_add] <;> abel
  right_distrib _ _ _ := by ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

/--
@isnad1 id=eq.0h5v.s6.e91c223becc8 from=seed src=0 shape=02b6d67e vocab=dda7fe5c
-/
theorem C_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (.C r * x : QuadraticAlgebra R a b) = r • x := by
  ext <;> simp

/--
@isnad1 id=eq.0h5v.s6.c6c4170c8a7f from=seed src=0 shape=f89843d6 vocab=8c400311
-/
@[simp]
theorem C_mul (x y : R) : .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b) := by
  ext <;> simp

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R]

instance instNonAssocSemiring : NonAssocSemiring (QuadraticAlgebra R a b) where
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

/--
@isnad1 id=eq.0h6v.s7.1e09ce575ac0 from=seed src=0 shape=6629957a vocab=30f33e58
-/
@[simp]
theorem nsmul_mk (n : ℕ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end NonAssocSemiring

section Semiring
variable (a b) [Semiring R]

/-- `QuadraticAlgebra.re` as a `LinearMap` -/
@[simps]
def reₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.im` as a `LinearMap` -/
@[simps]
def imₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.equivTuple` as a `LinearEquiv` -/
def linearEquivTuple : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 → R) where
  __ := equivProd a b |>.trans <| finTwoArrowEquiv _ |>.symm
  map_add' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  map_smul' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩

/--
@isnad1 id=eq.0h4v.s8.8c196631c322 from=seed src=0 shape=79f7c1fb vocab=85b43471
-/
@[simp]
lemma linearEquivTuple_apply (z : QuadraticAlgebra R a b) :
    (linearEquivTuple a b) z = ![z.re, z.im] := rfl

/--
@isnad1 id=eq.0h4v.s8.5e1e57e0ddef from=seed src=0 shape=595776dc vocab=de60113b
-/
@[simp]
lemma linearEquivTuple_symm_apply (x : Fin 2 → R) :
    (linearEquivTuple a b).symm x = ⟨x 0, x 1⟩ := rfl

/-- `QuadraticAlgebra R a b` has a basis over `R` given by `1` and `i` -/
noncomputable def basis : Module.Basis (Fin 2) R (QuadraticAlgebra R a b) :=
  .ofEquivFun <| linearEquivTuple a b

/--
@isnad1 id=eq.0h4v.s8.3ce169ab7eb7 from=seed src=0 shape=a12ececf vocab=e9c5b2d1
-/
@[simp]
theorem basis_repr_apply (x : QuadraticAlgebra R a b) :
    (basis a b).repr x = ![x.re, x.im] := rfl

instance : Module.Finite R (QuadraticAlgebra R a b) := .of_basis (basis a b)

instance : Module.Free R (QuadraticAlgebra R a b) := .of_basis (basis a b)

/--
@isnad1 id=eq.0h3v.s5.e9110d29baad from=seed src=0 shape=60cc6d69 vocab=901acab2
-/
theorem rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a b) = 2 := by
  simp [rank_eq_card_basis (basis a b)]

/--
@isnad1 id=eq.0h3v.s5.b33299518c58 from=seed src=0 shape=60cc6d69 vocab=5160e62d
-/
theorem finrank_eq_two [StrongRankCondition R] :
    Module.finrank R (QuadraticAlgebra R a b) = 2 := by
  simp [Module.finrank, rank_eq_two]

end Semiring

section CommSemiring
variable [CommSemiring R]

instance instCommSemiring : CommSemiring (QuadraticAlgebra R a b) where
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring

instance [CommSemiring S] [Algebra S R] : Algebra S (QuadraticAlgebra R a b) where
  algebraMap.toFun s := .C (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y := by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y := by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]

/--
@isnad1 id=eq.0h4v.s6.f9b44f7e0995 from=seed src=0 shape=f092507f vocab=ebbc5ce3
-/
theorem algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩ := rfl

/--
@isnad1 id=injectiv.0h3v.s6.cf54eadb2ee3 from=seed src=0 shape=69613e96 vocab=89d30d97
-/
theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

/--
@isnad1 id=iff.0h5v.s7.f1fc27959866 from=seed src=0 shape=46adecc5 vocab=6fc1ca8c
-/
@[simp]
theorem algebraMap_inj {x y : R} :
    algebraMap R (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y :=
  algebraMap_injective.eq_iff

/--
@isnad1 id=eq.0h4v.s6.2d6ba1fd3d7d from=seed src=0 shape=4fc5674c vocab=d3246f16
-/
@[simp]
theorem algebraMap_re : (algebraMap R (QuadraticAlgebra R a b) r).re = r := rfl

/--
@isnad1 id=eq.0h4v.s6.45f368450397 from=seed src=0 shape=a9194d1b vocab=61a67f96
-/
@[simp]
theorem algebraMap_im : (algebraMap R (QuadraticAlgebra R a b) r).im = 0 := rfl

instance [Semiring S] [Module S R] [Module.IsTorsionFree S R] :
    Module.IsTorsionFree S (QuadraticAlgebra R a b) :=
  (linearEquivTuple ..).injective.moduleIsTorsionFree _ (by simp)

/--
@isnad1 id=eq.0h5v.s6.6a210ec7719d from=seed src=0 shape=942f9be7 vocab=a64c54cb
-/
@[simp]
theorem C_pow (n : ℕ) (r : R) : (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n :=
  (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

/--
@isnad1 id=eq.0h5v.s6.1e07b37a2fdf from=seed src=0 shape=e336b5ee vocab=2f2b4426
-/
theorem mul_C_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (x * .C r : QuadraticAlgebra R a b) = r • x := by
  rw [mul_comm, C_mul_eq_smul r x]

/--
@isnad1 id=eq.0h3v.s6.23f250107dbe from=seed src=0 shape=47434c44 vocab=a5551011
-/
@[simp]
theorem C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b)) := rfl

/--
@isnad1 id=eq.0h5v.s6.95934502eb2b from=seed src=0 shape=a7edcd0c vocab=2f2b4426
-/
theorem smul_C (r1 r2 : R) :
    r1 • (.C r2 : QuadraticAlgebra R a b) = .C (r1 * r2) := by rw [C_mul, C_mul_eq_smul]

/--
@isnad1 id=iff.0h5v.s7.2fa7565dfab6 from=seed src=0 shape=bee29b7b vocab=fdea473d
-/
theorem algebraMap_dvd_iff {r : R} {z : QuadraticAlgebra R a b} :
    (algebraMap R (QuadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re ∧ r ∣ z.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← C_eq_algebraMap]

/--
@isnad1 id=iff.0h5v.s7.0805cd1a51ec from=seed src=0 shape=46adecc5 vocab=2fd8d445
-/
@[simp]
theorem algebraMap_dvd_iff_dvd {z w : R} :
    algebraMap R (QuadraticAlgebra R a b) z ∣ algebraMap R (QuadraticAlgebra R a b) w ↔ z ∣ w := by
  rw [algebraMap_dvd_iff]
  simp

end CommSemiring

section CommRing

variable [CommRing R]

instance instCommRing : CommRing (QuadraticAlgebra R a b) where

instance [CharZero R] : CharZero (QuadraticAlgebra R a b) where
  cast_injective m n := by
    simp [QuadraticAlgebra.ext_iff]

/--
@isnad1 id=eq.0h6v.s7.d09c4dd39852 from=seed src=0 shape=6629957a vocab=d8ba9bfc
-/
@[simp]
theorem zsmul_val (n : ℤ) (x y : R) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

end CommRing

end QuadraticAlgebra
