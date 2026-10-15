/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku

/-!
# The Hilbert–Schmidt inner product on matrices

The **Hilbert–Schmidt (Frobenius) inner product** of two complex matrices is
`⟪A, B⟫ = Tr[Aᴴ B]`. Mathlib equips `Matrix` with the Frobenius *norm* but not (as a
global instance) with this inner product, so this quantum-free helper records the
plain bilinear data needed downstream: conjugate symmetry, sesquilinearity, and — the
key fact for the Lie-algebraic variance formula — **multiplicativity over the
Kronecker product**, `⟪A ⊗ C, B ⊗ D⟫ = ⟪A, B⟫ · ⟪C, D⟫`.

(The genuine `InnerProductSpace` structure, when needed for Gram–Schmidt / orthonormal
bases, is obtained separately by transport along the linear isometry to
`EuclideanSpace ℂ (m × m)`.)
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

variable {m : Type*} [Fintype m]

/-- The Hilbert–Schmidt (Frobenius) inner product `⟪A, B⟫ = Tr[Aᴴ B]`. Conjugate-linear
in the first argument, linear in the second. -/
def hsInner (A B : Matrix m m ℂ) : ℂ := (Aᴴ * B).trace

/--
@isnad1 id=eq.0h3v.s6.98c89fdfa790 from=translated src=- shape=d129739e vocab=a10e9c1f
-/
@[simp] theorem hsInner_def (A B : Matrix m m ℂ) : hsInner A B = (Aᴴ * B).trace := rfl

/-- Conjugate symmetry: `⟪A, B⟫ = conj ⟪B, A⟫`.
@isnad1 id=eq.0h3v.s5.48f099fe7da3 from=translated src=- shape=0f986717 vocab=cb006a04
-/
theorem hsInner_conj_symm (A B : Matrix m m ℂ) :
    hsInner A B = (starRingEnd ℂ) (hsInner B A) := by
  rw [hsInner, hsInner, starRingEnd_apply, ← Matrix.trace_conjTranspose,
    conjTranspose_mul, conjTranspose_conjTranspose]

/-- Additivity in the second argument.
@isnad1 id=eq.0h4v.s6.42078eb23998 from=translated src=- shape=821afdcc vocab=c57b6751
-/
theorem hsInner_add_right (A B C : Matrix m m ℂ) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  simp [hsInner, Matrix.mul_add, Matrix.trace_add]

/-- Additivity in the first argument.
@isnad1 id=eq.0h4v.s6.0a7a6396bc9a from=translated src=- shape=332d62b8 vocab=c57b6751
-/
theorem hsInner_add_left (A B C : Matrix m m ℂ) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  simp [hsInner, conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

/-- Subtractivity in the second argument.
@isnad1 id=eq.0h4v.s6.d761678dbd9f from=translated src=- shape=821afdcc vocab=8583d6e3
-/
theorem hsInner_sub_right (A B C : Matrix m m ℂ) :
    hsInner A (B - C) = hsInner A B - hsInner A C := by
  simp [hsInner, Matrix.mul_sub, Matrix.trace_sub]

/-- Subtractivity in the first argument.
@isnad1 id=eq.0h4v.s6.a5731eb15b11 from=translated src=- shape=332d62b8 vocab=8583d6e3
-/
theorem hsInner_sub_left (A B C : Matrix m m ℂ) :
    hsInner (A - B) C = hsInner A C - hsInner B C := by
  simp [hsInner, conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]

/-- Linearity in the second argument.
@isnad1 id=eq.0h4v.s5.7b4f62f8e95f from=translated src=- shape=2876f6a1 vocab=fb88cecb
-/
theorem hsInner_smul_right (c : ℂ) (A B : Matrix m m ℂ) :
    hsInner A (c • B) = c * hsInner A B := by
  simp [hsInner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Conjugate-linearity in the first argument.
@isnad1 id=eq.0h4v.s6.cbdcfc0e71f6 from=translated src=- shape=ad4bdc9e vocab=dfd62a80
-/
theorem hsInner_smul_left (c : ℂ) (A B : Matrix m m ℂ) :
    hsInner (c • A) B = (starRingEnd ℂ) c * hsInner A B := by
  simp [hsInner, conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Additivity over a finite sum in the second argument.
@isnad1 id=eq.0h5v.s5.92035bc748ab from=translated src=- shape=a4aba7d5 vocab=843a73c4
-/
theorem hsInner_sum_right {ι : Type*} (A : Matrix m m ℂ) (s : Finset ι)
    (f : ι → Matrix m m ℂ) :
    hsInner A (∑ i ∈ s, f i) = ∑ i ∈ s, hsInner A (f i) := by
  simp only [hsInner, Matrix.mul_sum, Matrix.trace_sum]

/-- Additivity over a finite sum in the first argument.
@isnad1 id=eq.0h5v.s5.28da945a1103 from=translated src=- shape=6fb71b40 vocab=843a73c4
-/
theorem hsInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → Matrix m m ℂ)
    (B : Matrix m m ℂ) :
    hsInner (∑ i ∈ s, f i) B = ∑ i ∈ s, hsInner (f i) B := by
  simp only [hsInner, conjTranspose_sum, Matrix.sum_mul, Matrix.trace_sum]

/-- **Multiplicativity over the Kronecker product** — the key identity for assembling
the quadratic Casimir's inner products: `⟪A ⊗ C, B ⊗ D⟫ = ⟪A, B⟫ · ⟪C, D⟫`.
@isnad1 id=eq.0h6v.s6.239215f36e96 from=translated src=- shape=f99c361d vocab=a3f5ab99
-/
theorem hsInner_kronecker {n : Type*} [Fintype n]
    (A B : Matrix m m ℂ) (C D : Matrix n n ℂ) :
    hsInner (A ⊗ₖ C) (B ⊗ₖ D) = hsInner A B * hsInner C D := by
  rw [hsInner, hsInner, hsInner, conjTranspose_kronecker, ← mul_kronecker_mul,
    trace_kronecker]

/-- For Hermitian arguments the Hilbert–Schmidt inner product is symmetric.
@isnad1 id=eq.2h3v.s6.027e85f8dc1c from=translated src=- shape=d47a5749 vocab=33fe097c
-/
theorem hsInner_comm_of_isHermitian {A B : Matrix m m ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    hsInner A B = hsInner B A := by
  rw [hsInner, hsInner, hA, hB, Matrix.trace_mul_comm]

/-- For Hermitian arguments the Hilbert–Schmidt inner product is real.
@isnad1 id=eq.2h3v.s7.179c0e94001a from=translated src=- shape=8d4cc78a vocab=41108a8a
-/
theorem hsInner_conj_of_isHermitian {A B : Matrix m m ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (starRingEnd ℂ) (hsInner A B) = hsInner A B := by
  rw [← hsInner_conj_symm]
  exact hsInner_comm_of_isHermitian hB hA

/-- The matrix units `single i j 1` are Hilbert–Schmidt orthonormal.
@isnad1 id=eq.0h5v.s6.93d3f130ebe9 from=translated src=- shape=cf08a09e vocab=09128a93
-/
theorem hsInner_single [DecidableEq m] (i j k l : m) :
    hsInner (Matrix.single i j (1 : ℂ)) (Matrix.single k l 1)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [hsInner, Matrix.conjTranspose_single, star_one, Matrix.trace_single_mul, one_smul]
  by_cases h : i = k ∧ j = l
  · simp_all
  · rw [ite_eq_right h]
    apply Matrix.single_apply_of_ne
    rintro ⟨hki, hlj⟩
    exact h ⟨hki.symm, hlj.symm⟩

end QuantumAlg
