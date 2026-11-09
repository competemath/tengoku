/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
import Tengoku.Seed.Algebra.Module.LinearMap.Polynomial
import Tengoku.Seed.LinearAlgebra.Charpoly.BaseChange
import Tengoku.Seed.RingTheory.TensorProduct.MvPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The Galois product formula for the relative idele norm

This file proves that, in the tensor-product presentation
`𝔸_L = 𝔸_K ⊗_K L`, extension of the determinant norm back to `𝔸_L`
is the product of all Galois conjugates.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- The determinant norm as a homogeneous polynomial in the coordinates
of a basis.  Keeping this polynomial over the ground field is what makes
the Galois product formula stable under arbitrary scalar extension.-/
def normPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : MvPolynomial ι K :=
  (-1 : MvPolynomial ι K) ^ Module.finrank K L *
    ((Algebra.lmul K L).toLinearMap.polyCharpoly b).coeff 0

/--
@isnad1 id=eq.0h5v.s9.0698232f8cee from=translated src=- shape=dfca2648 vocab=cb403e54
-/
@[simp]
theorem eval_normPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval (b.repr x) (normPolynomial b) =
      Algebra.norm K x := by
  rw [normPolynomial, map_mul, map_pow, map_neg, map_one,
    LinearMap.polyCharpoly_coeff_eval]
  exact ((Algebra.norm_apply K x).trans
    (LinearMap.det_eq_sign_charpoly_coeff
      ((Algebra.lmul K L) x))).symm

/-- The linear polynomial whose value at the coordinates of `x` is the
`σ`-conjugate of `x`.-/
def conjugatePolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L) :
    MvPolynomial ι L :=
  ∑ i, MvPolynomial.X i * MvPolynomial.C (σ (b i))

omit [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h6v.s9.1bbfcf7fb2f6 from=translated src=- shape=316ebe5c vocab=2aef0640
-/
@[simp]
theorem eval_conjugatePolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K L (b.repr x i))
        (conjugatePolynomial b σ) =
      σ x := by
  rw [conjugatePolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  calc
    ∑ i, algebraMap K L (b.repr x i) * σ (b i) =
        ∑ i, σ ((b.repr x i) • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Algebra.smul_def]
    _ = σ (∑ i, (b.repr x i) • b i) := by
      rw [map_sum]
    _ = σ x := by rw [b.sum_repr]

/-- The product of the universal conjugates, written as a polynomial over
the splitting field.-/
def galoisProductPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial ι L :=
  ∏ σ : L ≃ₐ[K] L, conjugatePolynomial b σ

/--
@isnad1 id=eq.0h5v.s9.0abe878844f1 from=translated src=- shape=3aea663c vocab=cd212a65
-/
@[simp]
theorem eval_galoisProductPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K L (b.repr x i))
        (galoisProductPolynomial b) =
      ∏ σ : L ≃ₐ[K] L, σ x := by
  simp [galoisProductPolynomial]

/-- Galois conjugation after scalar extension to an arbitrary commutative
`K`-algebra.-/
def scalarConjugation
    (A : Type*) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) :
    A ⊗[K] L →ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.map (AlgHom.id A A) σ.toAlgHom

omit [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h6v.s9.06f8c0b97531 from=translated src=- shape=1a3e1cb5 vocab=eedf5ec2
-/
@[simp]
theorem scalarConjugation_tmul
    (A : Type*) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (a : A) (x : L) :
    scalarConjugation (K := K) (L := L) A σ (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x :=
  rfl

omit [FiniteDimensional K L] in
/-- Evaluating a universal conjugate polynomial at the coordinates of a
base-changed element gives its actual scalar-extended conjugate.
@isnad1 id=eq.0h7v.s11.c968f4ec08d7 from=translated src=- shape=946a3854 vocab=7d4fe4f9
-/
theorem eval₂_conjugatePolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L)
    (z : A ⊗[K] L) :
    MvPolynomial.eval₂
        ((Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := L)).toRingHom)
        (fun i ↦ (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := L))
          ((Algebra.TensorProduct.basis A b).repr z i))
        (conjugatePolynomial b σ) =
      scalarConjugation (K := K) (L := L) A σ z := by
  simp only [conjugatePolynomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C]
  calc
    ∑ i, (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := L))
          ((Algebra.TensorProduct.basis A b).repr z i) *
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := L)) (σ (b i)) =
        ∑ i, scalarConjugation (K := K) (L := L) A σ
          (((Algebra.TensorProduct.basis A b).repr z i) •
            Algebra.TensorProduct.basis A b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [scalarConjugation, Algebra.TensorProduct.basis_apply,
        Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.smul_def]
    _ = scalarConjugation (K := K) (L := L) A σ
          (∑ i, ((Algebra.TensorProduct.basis A b).repr z i) •
            Algebra.TensorProduct.basis A b i) := by
      rw [map_sum]
    _ = scalarConjugation (K := K) (L := L) A σ z := by
      rw [(Algebra.TensorProduct.basis A b).sum_repr]

omit [FiniteDimensional K L] in
/--
@isnad1 id=eq.0h4v.s11.27815b7ca838 from=translated src=- shape=61a68a78 vocab=cc8c0a91
-/
@[simp]
theorem scalarConjugation_baseAdele_apply
    [NumberField K]
    (σ : L ≃ₐ[K] L) (z : RelativeAdeleRing K L) :
    scalarConjugation
        (NumberField.AdeleRing (𝓞 K) K) σ z =
      conjugation K L σ z :=
  rfl

end RelativeIdeleGroup
