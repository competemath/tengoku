import Tengoku.Hellingerrepolean4.Hellinger.HeterogeneousState
import Tengoku.Seed.MeasureTheory.Integral.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms traceNorm_matrixIntegral_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms integral_pure_lifting` (it only prints; the queue checks the axioms of every declaration). -/

/-! Entrywise matrix expectations and square-root lifting for arbitrary output laws. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace Hellinger.IntegralLifting

open Hellinger.TraceNorm Hellinger.MatrixLifting Hellinger.PosteriorState

variable {Ω ι : Type*} [MeasurableSpace Ω]

def matrixIntegral (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ y, A y i j ∂μ

/--
@isnad1 id=ishermit.1h4v.s6.2da7177118b9 from=translated src=- shape=d70297a7 vocab=4e2aacd2
-/
theorem matrixIntegral_isHermitian (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ y, (A y).IsHermitian) : (matrixIntegral μ A).IsHermitian := by
  ext i j
  change (∫ y, A y j i ∂μ) = ∫ y, A y i j ∂μ
  apply integral_congr_ae
  filter_upwards [] with y
  have h := congrFun (congrFun (hA y).eq i) j
  exact h

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=eq.2h5v.s7.6ac9dcbcce58 from=translated src=- shape=a81a5430 vocab=9cd58967
-/
theorem matrixIntegral_sub (μ : Measure Ω) (A B : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, Integrable (fun y => A y i j) μ)
    (hB : ∀ i j, Integrable (fun y => B y i j) μ) :
    matrixIntegral μ (fun y => A y - B y) = matrixIntegral μ A - matrixIntegral μ B := by
  ext i j
  exact integral_sub (hA i j) (hB i j)

/--
@isnad1 id=eq.0h5v.s7.cb60b8b51f9a from=translated src=- shape=3d9242c4 vocab=3b73a39e
-/
theorem matrixIntegral_reflection (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ) (f : ι → ℝ) :
    matrixIntegral μ (fun y => reflection f * A y * reflection f) =
      reflection f * matrixIntegral μ A * reflection f := by
  ext i j
  simp only [matrixIntegral, reflection, Matrix.diagonal_mul, Matrix.mul_diagonal,
    integral_mul_const, integral_const_mul]

omit [DecidableEq ι] in
/--
@isnad1 id=integrab.1h5v.s6.1e63e14415c6 from=translated src=- shape=7421b996 vocab=808d2679
-/
theorem trace_mul_integrable (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, Integrable (fun y => A y i j) μ) (Q : Matrix ι ι ℝ) :
    Integrable (fun y => (Q * A y).trace) μ := by
  unfold Matrix.trace
  apply integrable_finsetSum
  intro i _
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply integrable_finsetSum
  intro j _
  exact (hA j i).const_mul (Q i j)

omit [DecidableEq ι] in
/--
@isnad1 id=eq.1h5v.s7.1206dc6abb7d from=translated src=- shape=fe630061 vocab=ab401f1e
-/
theorem trace_mul_matrixIntegral (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, Integrable (fun y => A y i j) μ) (Q : Matrix ι ι ℝ) :
    (Q * matrixIntegral μ A).trace = ∫ y, (Q * A y).trace ∂μ := by
  symm
  unfold Matrix.trace
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag_apply, Matrix.mul_apply, matrixIntegral]
    rw [integral_finsetSum Finset.univ]
    · simp only [integral_const_mul]
    · intro j _
      exact (hA j i).const_mul (Q i j)
  · intro i _
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    apply integrable_finsetSum
    intro j _
    exact (hA j i).const_mul (Q i j)

/--
@isnad1 id=le.4h5v.s7.3b8953d6d874 from=translated src=- shape=f77af6ce vocab=128c8b74
-/
theorem traceNorm_matrixIntegral_le (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ i j, Integrable (fun y => A y i j) μ)
    (hAH : ∀ y, (A y).IsHermitian) (g : Ω → ℝ) (hg : Integrable g μ)
    (hbound : ∀ y, traceNorm (A y) ≤ g y) :
    traceNorm (matrixIntegral μ A) ≤ ∫ y, g y ∂μ := by
  let Q := signWitness (matrixIntegral_isHermitian μ A hAH)
  rw [← signWitness_attains (matrixIntegral_isHermitian μ A hAH), trace_mul_matrixIntegral μ A hA]
  apply integral_mono (trace_mul_integrable μ A hA Q) hg
  intro y
  exact (trace_mul_le_traceNorm (hAH y) (signWitness_orderContraction _)).trans (hbound y)

/--
@isnad1 id=le.4h5v.s7.7ceb3d2e7d59 from=translated src=- shape=f8e21819 vocab=ae6ba501
-/
theorem integral_pure_lifting (μ : Measure Ω) (v w : Ω → ι → ℝ)
    (hv : ∀ y, v y ⬝ᵥ v y = 1) (hw : ∀ y, w y ⬝ᵥ w y = 1)
    (hentry : ∀ i j, Integrable (fun y => pureDifference (v y) (w y) i j) μ)
    (hroot : Integrable (fun y => root (v y ⬝ᵥ w y)) μ) :
    traceNorm (matrixIntegral μ (fun y => pureDifference (v y) (w y))) / 2 ≤
      ∫ y, root (v y ⬝ᵥ w y) ∂μ := by
  have h := traceNorm_matrixIntegral_le μ (fun y => pureDifference (v y) (w y)) hentry
    (fun y => pureDifference_isHermitian (v y) (w y))
    (fun y => 2 * root (v y ⬝ᵥ w y)) (hroot.const_mul 2)
    (fun y => le_of_eq (traceNorm_pureDifference _ _ (hv y) (hw y)))
  rw [integral_const_mul] at h
  linarith

end Hellinger.IntegralLifting
