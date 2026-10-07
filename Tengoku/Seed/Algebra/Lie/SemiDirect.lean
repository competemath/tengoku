/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Lie.Derivation.Basic
public import Tengoku.Seed.Algebra.Lie.Extension
public import Tengoku.Seed.Algebra.Lie.Prod

/-!
# Semi-direct products

This file defines the semi-direct sum of Lie algebras. These are the infinitesimal counterpart of
semidirect products of (Lie) groups. Given two Lie algebras `K` and `L` over `R` as well as a Lie
algebra homomorphism  `ψ : L → LieDerivation  R K K`, the underlying set of the semidirect sum is
`K × L`, however the bracket is twisted by `ψ`. In this file we show that `SemiDirectSum K L ψ` is
itself a Lie algebra and that it fits into an exact sequence `H → (SemiDirectSum K L ψ) → L`, i.e.
forms an extension of `L`.


## References

* https://en.wikipedia.org/wiki/Lie_algebra_extension#By_semidirect_sum

-/


@[expose] public section

namespace LieAlgebra

/--
The semi-direct sum of two Lie algebras `K` and `L` over `R`, relative to a Lie algebra homomorphism
`ψ: L → LieDerivation R K K`. As a set, it is just `K × L`, however the Lie bracket is twisted by
`ψ`.
-/
@[ext] structure SemiDirectSum {R : Type*} [CommRing R] (K : Type*) [LieRing K] [LieAlgebra R K]
    (L : Type*) [LieRing L] [LieAlgebra R L] (_ : L →ₗ⁅R⁆ LieDerivation R K K) where
  /-- The element of K -/
  left : K
  /-- The element of L -/
  right : L

@[inherit_doc]
notation:35 K " ⋊⁅" ψ:35 "⁆ " L:35 => SemiDirectSum K L ψ


namespace SemiDirectSum

variable {R : Type*} [CommRing R]
variable {K : Type*} [LieRing K] [LieAlgebra R K]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

section
variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

variable {ψ} in
/-- As raw types, the semidirect product is just a product. -/
def toProd : K ⋊⁅ψ⁆ L ≃ K × L where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=eq.0h5v.s7.db2e2b43f70d from=seed src=0 shape=23bfad65 vocab=e28f0b9b
-/
@[simp] lemma toProd_apply (x : K ⋊⁅ψ⁆ L) : toProd (x) = ⟨x.left, x.right⟩ := rfl

instance : AddCommGroup (K ⋊⁅ψ⁆ L) := toProd.addCommGroup

instance : Module R (K ⋊⁅ψ⁆ L) :=
  { toProd with map_add' _ _ := rfl : (K ⋊⁅ψ⁆ L) ≃+ K × L }.module R

/-- `LieAlgebra.SemiDirectSum.toProd` as a linear equivalence. -/
def toProdl : (K ⋊⁅ψ⁆ L) ≃ₗ[R] K × L :=
  { __ := toProd
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/--
@isnad1 id=eq.0h5v.s9.ac1c0e4e1656 from=seed src=0 shape=220c3141 vocab=9f8548bd
-/
@[simp] lemma toProdl_coe (x : K ⋊⁅ψ⁆ L) : toProdl ψ x = toProd x := rfl

instance : Bracket (K ⋊⁅ψ⁆ L) (K ⋊⁅ψ⁆ L) where
  bracket x y := ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩

/--
@isnad1 id=eq.0h4v.s7.73e1b50b1249 from=seed src=0 shape=77b44493 vocab=2727dd3d
-/
@[simp] lemma zero_eq_mk : (0 : K ⋊⁅ψ⁆ L) = ⟨0, 0⟩ := rfl
/--
@isnad1 id=eq.0h6v.s8.6a64f16f1fd9 from=seed src=0 shape=66303907 vocab=c2412ed7
-/
@[simp] lemma add_eq_mk (x y : K ⋊⁅ψ⁆ L) : x + y = ⟨x.left + y.left, x.right + y.right⟩ := rfl
/--
@isnad1 id=eq.0h6v.s8.d991cc92a21a from=seed src=0 shape=66303907 vocab=67c4a9fe
-/
@[simp] lemma sub_eq_mk (x y : K ⋊⁅ψ⁆ L) : x - y = ⟨x.left - y.left, x.right - y.right⟩ := rfl
/--
@isnad1 id=eq.0h5v.s7.22c7289aee69 from=seed src=0 shape=1cca19a6 vocab=319ac958
-/
@[simp] lemma neg_eq_mk (x : K ⋊⁅ψ⁆ L) : -x = ⟨-x.left, -x.right⟩ := rfl
/--
@isnad1 id=eq.0h6v.s9.0a01a1722de7 from=seed src=0 shape=b41b753c vocab=81938d8d
-/
@[simp] lemma smul_eq_mk (t : R) (x : K ⋊⁅ψ⁆ L) : t • x = ⟨t • x.left, t • x.right⟩ := rfl
/--
@isnad1 id=eq.0h6v.s9.53a38b5b373f from=seed src=0 shape=1f00370f vocab=bd375cca
-/
@[simp] lemma lie_eq_mk (x y : K ⋊⁅ψ⁆ L) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩ :=
  rfl

instance : LieRing (K ⋊⁅ψ⁆ L) where
  add_lie _ _ _ := by simp; abel
  lie_add _ _ _ := by simp; abel
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp; grind [lie_skew]

instance : LieAlgebra R (K ⋊⁅ψ⁆ L) where
  lie_smul _ _ _ := by simp [smul_sub, smul_add]

/-- The canonical inclusion of K into the semi-direct sum K ⋊⁅ψ⁆ G. -/
def inl : K →ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  toFun x := ⟨x, 0⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/-- The canonical inclusion of L into the semi-direct sum K ⋊⁅ψ⁆ G. -/
def inr : L →ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  toFun x := ⟨0, x⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/--
@isnad1 id=eq.0h5v.s7.7f8285bd29b1 from=seed src=0 shape=5621c6d5 vocab=75204866
-/
@[simp] lemma inl_eq_mk (x : K) : inl ψ x = ⟨x, 0⟩ := rfl
/--
@isnad1 id=eq.0h5v.s7.48653a73f8d0 from=seed src=0 shape=6d007aeb vocab=8ff5c784
-/
@[simp] lemma inr_eq_mk (x : L) : inr ψ x = ⟨0, x⟩ := rfl

/--
@isnad1 id=injectiv.0h4v.s7.53b85fe7ab0b from=seed src=0 shape=922f3095 vocab=3f7536a4
-/
@[simp]
lemma inl_injective : Function.Injective (inl ψ) := by intro; simp [inl]

/-- The canonical projection of the semi-direct sum K ⋊⁅ψ⁆ L to G. -/
def projr : K ⋊⁅ψ⁆ L →ₗ⁅R⁆ L where
  toFun x := x.right
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/-- The canonical projection of the semi-direct sum K ⋊⁅ψ⁆ L to G.
It is not, in general, a Lie algebra homomorphism, just a linear map. -/
def projl : K ⋊⁅ψ⁆ L →ₗ[R] K where
  toFun x := x.left
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/--
@isnad1 id=eq.0h5v.s7.727b3df9a514 from=seed src=0 shape=9f7ba92d vocab=ad56c6af
-/
@[simp] lemma projr_mk (x : K ⋊⁅ψ⁆ L) : projr ψ x = x.right := rfl
/--
@isnad1 id=eq.0h5v.s8.53a6e929a7a7 from=seed src=0 shape=b33247dc vocab=236abbf7
-/
@[simp] lemma projl_mk (x : K ⋊⁅ψ⁆ L) : projl ψ x = x.left := rfl

/--
@isnad1 id=eq.0h5v.s8.8469f6335e45 from=seed src=0 shape=798f5539 vocab=ad45aa65
-/
lemma projr_inl_apply {x : K} : projr ψ (inl ψ x) = 0 := by simp
/--
@isnad1 id=eq.0h5v.s8.9a3def1e71ce from=seed src=0 shape=5873f8f5 vocab=3ce48c9c
-/
lemma projr_inr_apply {x : L} : projr ψ (inr ψ x) = x := by simp
/--
@isnad1 id=eq.0h5v.s8.2897d7a94375 from=seed src=0 shape=ea0b65d4 vocab=72a0da37
-/
lemma projl_inr_apply {x : L} : projl ψ (inr ψ x) = 0 := by simp
/--
@isnad1 id=eq.0h5v.s8.5753a8846793 from=seed src=0 shape=fea160c4 vocab=d7d18dac
-/
lemma projl_inl_apply {x : K} : projl ψ (inl ψ x) = x := by simp

/--
@isnad1 id=surjecti.0h4v.s7.f55384259ac4 from=seed src=0 shape=49dffc8c vocab=7328ae2d
-/
@[simp]
lemma projr_surjective : Function.Surjective (projr ψ) :=
  fun x ↦ ⟨inr ψ x, by simp⟩

instance : LieAlgebra.IsExtension (inl ψ) (projr ψ) where
  ker_eq_bot := by simp [LieHom.ker_eq_bot]
  range_eq_top := by simp [LieHom.range_eq_top]
  exact := by ext ⟨x, y⟩; aesop

end

variable (R K L) in
/-- The product of two Lie algebras realized through a semidirect sum with trivial `ψ` -/
@[simps!]
def prod_iso : (K ⋊⁅(0 : L →ₗ⁅R⁆ (LieDerivation R K K))⁆ L) ≃ₗ⁅R⁆ (K × L) where
  __ := toProdl 0
  map_lie' {_ _} := by simp

end SemiDirectSum
end LieAlgebra
end
