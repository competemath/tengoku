/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Tengoku

/-!
# Euclidean coordinate norms and gradients

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The coordinate-vector norm and gradient API is kept in the
independent `CKN` namespace.

The main definitions are `CKN.vecEuclideanNorm` and `CKN.classicalGradient`.
The norm lemmas give positivity, scalar multiplication and component bounds.
-/

@[expose] public section

open scoped BigOperators

namespace CKN

/-- The Euclidean dot product on native coordinate vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on native coordinate vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- The Euclidean norm on native coordinate vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

/--
@isnad1 id=eq.0h2v.s5.629540dd00b2 from=translated src=- shape=c4e2c758 vocab=c844a692
-/
theorem vecNormSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

/--
@isnad1 id=le.0h2v.s4.43ad66d63db9 from=translated src=- shape=9363a417 vocab=93835b15
-/
theorem vecNormSq_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)

/--
@isnad1 id=le.0h3v.s5.349af02303e9 from=translated src=- shape=0dc23305 vocab=8575ecb4
-/
theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

/--
@isnad1 id=eq.1h2v.s5.664cd29a3d6c from=translated src=- shape=2bcaeb3a vocab=56c8c71a
-/
theorem vecNormSq_eq_zero {d : ℕ} {x : Vec d}
    (h : vecNormSq x = 0) :
    x = 0 := by
  funext i
  have hi : x i ^ 2 ≤ 0 := by
    simpa [h] using sq_apply_le_vecNormSq x i
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg (x i)))

/--
@isnad1 id=eq.0h3v.s5.d347e75b4beb from=translated src=- shape=c499a49c vocab=9cf589d2
-/
theorem vecNormSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
  calc
    (∑ i, (c • x) i ^ 2) = ∑ i, c ^ 2 * x i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

/-- The Euclidean norm is nonnegative.
@isnad1 id=le.0h2v.s4.45467c247a1f from=translated src=- shape=9363a417 vocab=418ef3bd
-/
theorem vecEuclideanNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecEuclideanNorm x :=
  Real.sqrt_nonneg _

/--
@isnad1 id=eq.0h2v.s4.e2b9f3fec38e from=translated src=- shape=94551d6e vocab=b2a3c2fd
-/
theorem vecEuclideanNorm_sq {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x ^ 2 = vecNormSq x := by
  exact Real.sq_sqrt (vecNormSq_nonneg x)

/-- The Euclidean norm respects scalar multiplication.
@isnad1 id=eq.0h3v.s5.740c3028026a from=translated src=- shape=c8674532 vocab=d60b2992
-/
theorem vecEuclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x := by
  rw [vecEuclideanNorm, vecEuclideanNorm, vecNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/--
@isnad1 id=iff.0h2v.s5.bb2ec3e724a4 from=translated src=- shape=fdf297c6 vocab=d93a5498
-/
theorem vecEuclideanNorm_eq_zero_iff {d : ℕ} {x : Vec d} :
    vecEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply vecNormSq_eq_zero
    rw [← vecEuclideanNorm_sq, h]
    norm_num
  · intro hx
    rw [hx]
    simp [vecEuclideanNorm, vecNormSq, vecDot]

/--
@isnad1 id=le.0h3v.s4.42fea48eb2b7 from=translated src=- shape=1d4b51a9 vocab=863d0d4b
-/
theorem abs_apply_le_vecEuclideanNorm {d : ℕ}
    (x : Vec d) (i : Fin d) :
    |x i| ≤ vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq x i)

/-- The coordinate gradient of a scalar function in the native vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

/--
@isnad1 id=eq.0h4v.s8.c32c694afd5c from=translated src=- shape=0126707f vocab=67b2abd4
-/
@[simp]
theorem classicalGradient_apply {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    classicalGradient f x i =
      (fderiv ℝ f x) (basisVec i) :=
  rfl

end CKN
