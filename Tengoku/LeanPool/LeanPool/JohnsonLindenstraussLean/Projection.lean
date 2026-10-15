/-
Copyright (c) 2026 claytomode. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: claytomode
-/
module

public import Tengoku

/-!
# The Gaussian random projection

This file defines the Johnson–Lindenstrauss random projection

`jlMap k n A x = (1/√k) • (A.mulVec x)`,

where `A : Matrix (Fin k) (Fin n) ℝ` is the (random) matrix of i.i.d. `N(0,1)`
entries, and proves the **deterministic row-product reduction**

`‖f x‖² = (1/k) · Σ_i (Aᵢ · x)²`,

expressing the squared norm of the projection as `1/k` times a sum of squared
row–vector products. Under the Gaussian law on `A`, each `Aᵢ · x` is `N(0, ‖x‖²)`
(Gaussian rotation invariance), so `k · ‖f x‖² / ‖x‖²` has the chi-squared law of
`JL.ChiSquared`; that probabilistic reduction is the one ingredient consumed as a
labeled hypothesis by the existence theorem.
-/

@[expose] public section

open scoped BigOperators

namespace JL

/-- The Johnson–Lindenstrauss random projection `f x = (1/√k) • (A.mulVec x)`. -/
noncomputable def jlMap (k n : ℕ) (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ) : Fin k → ℝ :=
  (Real.sqrt k)⁻¹ • A.mulVec x

/--
@isnad1 id=eq.0h5v.s6.87145a9b0d7d from=translated src=- shape=5383d3da vocab=16554982
-/
@[simp] lemma jlMap_apply (k n : ℕ) (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin k) :
    jlMap k n A x i = (Real.sqrt k)⁻¹ * ∑ j, A i j * x j := by
  simp [jlMap, Matrix.mulVec, dotProduct]

/-- **Deterministic row-product reduction.** The squared Euclidean norm of the
projection equals `1/k` times the sum of squared row–vector products.
@isnad1 id=eq.0h4v.s7.df7c9f59372c from=translated src=- shape=5de0efec vocab=36d3af8b
-/
theorem jlMap_sq_norm (k n : ℕ) (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ i, (jlMap k n A x i) ^ 2 = (1 / (k : ℝ)) * ∑ i, (∑ j, A i j * x j) ^ 2 := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  simp only [jlMap_apply, mul_pow]
  rw [← Finset.mul_sum]
  congr 1
  rw [inv_pow, Real.sq_sqrt hk0, one_div]

end JL
