/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Lie.Matrix
public import Tengoku.Seed.LinearAlgebra.Matrix.SesquilinearForm
public import Tengoku.Seed.Tactic.NoncommRing

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

When a module carries a bilinear form, the Lie algebra of endomorphisms of the module contains a
distinguished Lie subalgebra: the skew-adjoint endomorphisms. Such subalgebras are important
because they provide a simple, explicit construction of the so-called classical Lie algebras.

This file defines the Lie subalgebra of skew-adjoint endomorphisms cut out by a bilinear form on
a module and proves some basic related results. It also provides the corresponding definitions and
results for the Lie algebra of square matrices.

## Main definitions

  * `skewAdjointLieSubalgebra`
  * `skewAdjointLieSubalgebraEquiv`
  * `skewAdjointMatricesLieSubalgebra`
  * `skewAdjointMatricesLieSubalgebraEquiv`

## Tags

lie algebra, skew-adjoint, bilinear form
-/

@[expose] public section


universe u v w w₁

section SkewAdjointEndomorphisms

open LinearMap (BilinForm)

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : BilinForm R M)

/--
@isnad1 id=mem.2h5v.s10.999431dedd51 from=seed src=0 shape=5b3f3d3b vocab=d979b82e
-/
theorem LinearMap.BilinForm.isSkewAdjoint_bracket {f g : Module.End R M}
    (hf : f ∈ B.skewAdjointSubmodule) (hg : g ∈ B.skewAdjointSubmodule) :
    ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_sub]
  exact hfg.sub hgf

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
def skewAdjointLieSubalgebra : LieSubalgebra R (Module.End R M) :=
  { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
def skewAdjointLieSubalgebraEquiv :
    skewAdjointLieSubalgebra (B.compl₁₂ (e : N →ₗ[R] M) e) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra B := by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  ext f
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact (LinearMap.isPairSelfAdjoint_equiv (B := -B) (F := B) e f).symm

/--
@isnad1 id=eq.0h6v.s13.d4b04476d9d2 from=seed src=0 shape=0ee2d7ab vocab=06abc063
-/
@[simp]
theorem skewAdjointLieSubalgebraEquiv_apply
    (f : skewAdjointLieSubalgebra (B.compl₁₂ (Qₗ := N) (Qₗ' := N) ↑e ↑e)) :
    ↑(skewAdjointLieSubalgebraEquiv B e f) = e.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

/--
@isnad1 id=eq.0h6v.s13.b1a92744729a from=seed src=0 shape=9a7ddcda vocab=b08b7854
-/
@[simp]
theorem skewAdjointLieSubalgebraEquiv_symm_apply (f : skewAdjointLieSubalgebra B) :
    ↑((skewAdjointLieSubalgebraEquiv B e).symm f) = e.symm.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

end SkewAdjointEndomorphisms

section SkewAdjointMatrices

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [Fintype n]
variable (J : Matrix n n R)

/--
@isnad1 id=eq.0h4v.s6.d15e8dfb1753 from=seed src=0 shape=77086cd4 vocab=77249d31
-/
theorem Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
  show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp

variable [DecidableEq n]

/--
@isnad1 id=mem.2h5v.s9.0e6344b83298 from=seed src=0 shape=545dafc9 vocab=2e612ed6
-/
theorem Matrix.isSkewAdjoint_bracket {A B : Matrix n n R} (hA : A ∈ skewAdjointMatricesSubmodule J)
    (hB : B ∈ skewAdjointMatricesSubmodule J) : ⁅A, B⁆ ∈ skewAdjointMatricesSubmodule J := by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  change Aᵀ * J = J * (-A) at hA
  change Bᵀ * J = J * (-B) at hB
  rw [Matrix.lie_transpose, LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket, sub_mul, mul_assoc, mul_assoc, hA, hB, ← mul_assoc,
    ← mul_assoc, hA, hB]
  noncomm_ring

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
def skewAdjointMatricesLieSubalgebra : LieSubalgebra R (Matrix n n R) :=
  { skewAdjointMatricesSubmodule J with
    lie_mem' := J.isSkewAdjoint_bracket }

/--
@isnad1 id=iff.0h4v.s8.6532a08bbb64 from=seed src=0 shape=3995a264 vocab=94ab2fba
-/
@[simp]
theorem mem_skewAdjointMatricesLieSubalgebra (A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra J ↔ A ∈ skewAdjointMatricesSubmodule J :=
  Iff.rfl

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
def skewAdjointMatricesLieSubalgebraEquiv (P : Matrix n n R) (h : Invertible P) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (Pᵀ * J * P) :=
  LieEquiv.ofSubalgebras _ _ (P.lieConj h).symm <| by
    ext A
    suffices P.lieConj h A ∈ skewAdjointMatricesSubmodule J ↔
        A ∈ skewAdjointMatricesSubmodule (Pᵀ * J * P) by
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      exact this
    simp [Matrix.IsSkewAdjoint, J.isAdjointPair_equiv _ _ P (isUnit_of_invertible P)]

/--
@isnad1 id=eq.0h6v.s12.1bc619cc180c from=seed src=0 shape=037e4d46 vocab=62b3b469
-/
theorem skewAdjointMatricesLieSubalgebraEquiv_apply (P : Matrix n n R) (h : Invertible P)
    (A : skewAdjointMatricesLieSubalgebra J) :
    ↑(skewAdjointMatricesLieSubalgebraEquiv J P h A) = P⁻¹ * A * P := by
  simp [skewAdjointMatricesLieSubalgebraEquiv]

/-- An equivalence of matrix algebras commuting with the transpose endomorphisms restricts to an
equivalence of Lie algebras of skew-adjoint matrices. -/
def skewAdjointMatricesLieSubalgebraEquivTranspose {m : Type w} [DecidableEq m] [Fintype m]
    (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : ∀ A, (e A)ᵀ = e Aᵀ) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (e J) :=
  LieEquiv.ofSubalgebras _ _ e.toLieEquiv <| by
    ext A
    suffices J.IsSkewAdjoint (e.symm A) ↔ (e J).IsSkewAdjoint A by
      simpa [-LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← h,
      ← Function.Injective.eq_iff e.injective, map_mul, AlgEquiv.apply_symm_apply, map_neg]

/--
@isnad1 id=eq.1h6v.s12.367fe28e3abf from=seed src=0 shape=a0bbb96e vocab=d42fa76d
-/
@[simp]
theorem skewAdjointMatricesLieSubalgebraEquivTranspose_apply {m : Type w} [DecidableEq m]
    [Fintype m] (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : ∀ A, (e A)ᵀ = e Aᵀ)
    (A : skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointMatricesLieSubalgebraEquivTranspose J e h A : Matrix m m R) = e A :=
  rfl

/--
@isnad1 id=iff.0h5v.s8.44880a34ef1b from=seed src=0 shape=3913e6b6 vocab=05138296
-/
theorem mem_skewAdjointMatricesLieSubalgebra_unit_smul (u : Rˣ) (J A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra (u • J) ↔ A ∈ skewAdjointMatricesLieSubalgebra J := by
  change A ∈ skewAdjointMatricesSubmodule (u • J) ↔ A ∈ skewAdjointMatricesSubmodule J
  simp only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  constructor <;> intro h
  · simpa using congr_arg (fun B => u⁻¹ • B) h
  · simp [h]

end SkewAdjointMatrices
