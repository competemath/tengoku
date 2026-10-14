/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import Tengoku

/-! Exact formal inverse-branch calculations for the two explicit examples.
These do not assert a general Lagrange–Good or half-pair inversion theorem. -/

@[expose] public section
noncomputable section
namespace GaussianMomentsCounterexamples
open PowerSeries

/-- The geometric series, defined coefficientwise. -/
def geometricSeries : ℂ⟦X⟧ := mk (fun _ => 1)

/--
@isnad1 id=eq.0h1v.s6.4ce8e52f904c from=translated src=- shape=9f7bb737 vocab=0ac86c5f
-/
@[simp] theorem geometricSeries_coeff (m : ℕ) : coeff m geometricSeries = 1 := by
  simp [geometricSeries]

/--
@isnad1 id=eq.0h0v.s6.e319dd138d6f from=translated src=- shape=219582fe vocab=59a5cd15
-/
lemma geometricSeries_mul_one_sub : geometricSeries * (1 - X) = 1 :=
  mk_one_mul_one_sub_eq_one ℂ

/--
@isnad1 id=eq.0h0v.s6.5168e6835956 from=translated src=- shape=7bace7f8 vocab=59a5cd15
-/
lemma one_sub_mul_geometricSeries : (1 - X) * geometricSeries = 1 := by
  rw [mul_comm]; exact geometricSeries_mul_one_sub

/--
@isnad1 id=ne.0h0v.s5.59968230bfe6 from=translated src=- shape=d7e46ef3 vocab=ce72a494
-/
lemma one_sub_X_ne_zero : (1 - X : ℂ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simp at this

/--
@isnad1 id=eq.0h0v.s5.10b65c47774c from=translated src=- shape=163bdb26 vocab=856d6367
-/
theorem geometricSeries_eq_inv : geometricSeries = (1 - X : ℂ⟦X⟧)⁻¹ := by
  apply mul_left_cancel₀ one_sub_X_ne_zero
  rw [one_sub_mul_geometricSeries, PowerSeries.mul_inv_cancel]
  simp

/-- The branch t/(1-t), with formal division by a unit. -/
def branchZeta : ℂ⟦X⟧ := X * geometricSeries

/--
@isnad1 id=eq.0h0v.s5.db168d4da11e from=translated src=- shape=9b00a135 vocab=adb8e606
-/
lemma one_add_branchZeta : 1 + branchZeta = geometricSeries := by
  unfold branchZeta
  linear_combination -geometricSeries_mul_one_sub

/--
@isnad1 id=eq.0h0v.s5.ba6576f97bc5 from=translated src=- shape=8b3e5d3e vocab=6c6a4abe
-/
@[simp] lemma branchZeta_constantCoeff : constantCoeff branchZeta = 0 := by
  simp [branchZeta]

/--
@isnad1 id=eq.0h0v.s6.799f2a977fec from=translated src=- shape=7773c6d3 vocab=3fbbd7f4
-/
lemma branchZeta_eq : branchZeta = X * (1 - X : ℂ⟦X⟧)⁻¹ := by
  rw [branchZeta, geometricSeries_eq_inv]

/-- The explicit polynomial map H from the discovery calculation. -/
def discoveryH (z : Fin 2 → ℂ⟦X⟧) : Fin 2 → ℂ⟦X⟧ :=
  ![(1 - z 0) * (1 + z 1), 1 + z 1]

/-- The formal branch (t, t/(1-t)) of the discovery vector field. -/
def discoveryBranch : Fin 2 → ℂ⟦X⟧ := ![X, branchZeta]

/--
@isnad1 id=eq.0h1v.s5.60e76320b0ce from=translated src=- shape=9139ba4a vocab=d78a22a3
-/
theorem discoveryBranch_equation (i : Fin 2) :
    discoveryBranch i = X * discoveryH discoveryBranch i := by
  fin_cases i
  · change X = X * ((1 - X) * (1 + branchZeta))
    rw [one_add_branchZeta, one_sub_mul_geometricSeries, mul_one]
  · change branchZeta = X * (1 + branchZeta)
    rw [one_add_branchZeta]; rfl

/-- The polynomial map whose evaluation is `discoveryH`. -/
def discoveryHPolynomial : Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![(1 - MvPolynomial.X 0) * (1 + MvPolynomial.X 1), 1 + MvPolynomial.X 1]

/--
@isnad1 id=eq.0h2v.s5.416bef2dba5f from=translated src=- shape=25d9e853 vocab=cf3b6100
-/
theorem discoveryHPolynomial_eval (z : Fin 2 → ℂ⟦X⟧) (i : Fin 2) :
    MvPolynomial.eval₂ C z (discoveryHPolynomial i) = discoveryH z i := by
  fin_cases i <;> simp [discoveryHPolynomial, discoveryH, MvPolynomial.eval₂_sub]

/-- The displayed branch is the unique solution of g=tH(g).
@isnad1 id=eq.1h1v.s5.8aefc8c95c26 from=translated src=- shape=6e4b7991 vocab=d78a22a3
-/
theorem discoveryBranch_unique (g : Fin 2 → ℂ⟦X⟧)
    (hg : ∀ i, g i = X * discoveryH g i) : g = discoveryBranch := by
  have h1 : g 1 = X * (1 + g 1) := by simpa [discoveryH] using hg 1
  have hg1 : g 1 = branchZeta := by
    apply mul_right_cancel₀ one_sub_X_ne_zero
    calc
      g 1 * (1 - X) = X := by linear_combination h1
      _ = branchZeta * (1 - X) := by
        rw [branchZeta, mul_assoc, geometricSeries_mul_one_sub, mul_one]
  have h0 : g 0 = X * ((1 - g 0) * geometricSeries) := by
    simpa [discoveryH, hg1, one_add_branchZeta] using hg 0
  have hh := congrArg (fun a => a * (1 - X)) h0
  simp only [mul_assoc, geometricSeries_mul_one_sub, mul_one] at hh
  have hg0 : g 0 = X := by linear_combination hh
  funext i
  fin_cases i <;> simp [discoveryBranch, hg0, hg1]

/-- The Jacobian matrix of H evaluated on the branch. -/
def discoveryJacobian : Matrix (Fin 2) (Fin 2) ℂ⟦X⟧ :=
  !![-(1 + branchZeta), 1 - X; 0, 1]

/-- The displayed matrix is the actual polynomial Jacobian evaluated on the branch.
@isnad1 id=eq.0h2v.s8.5773eee5f2d1 from=translated src=- shape=3ce8d59d vocab=0dfa3218
-/
theorem discoveryJacobian_correspondence (i j : Fin 2) :
    discoveryJacobian i j = MvPolynomial.eval₂ C discoveryBranch
      (MvPolynomial.pderiv j (discoveryHPolynomial i)) := by
  fin_cases i <;> fin_cases j <;>
    simp [discoveryJacobian, discoveryHPolynomial, discoveryBranch, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_neg]

/--
@isnad1 id=eq.0h0v.s8.9e6834fc083f from=translated src=- shape=45f0935a vocab=abf1e447
-/
theorem discovery_determinant :
    Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℂ⟦X⟧) - (X : ℂ⟦X⟧) • discoveryJacobian) = (1 :
      ℂ⟦X⟧) := by
  simp [Matrix.det_fin_two, discoveryJacobian, Matrix.sub_apply,
    one_add_branchZeta, smul_eq_mul]
  linear_combination X * geometricSeries_mul_one_sub

/-- The quadratic coefficient v in the three-variable construction. -/
def halfPairV (z : ℂ⟦X⟧) : ℂ⟦X⟧ := -C (1 / 2) * (1 + z) * (2 + z)

/--
@isnad1 id=eq.0h0v.s5.fe5020430895 from=translated src=- shape=77644231 vocab=f905f5fa
-/
theorem halfPair_branch_equation : branchZeta = X * (1 + branchZeta) := by
  rw [one_add_branchZeta]; rfl

/--
@isnad1 id=eq.0h0v.s6.043e9e792a36 from=translated src=- shape=8267e56e vocab=15f78fc2
-/
theorem halfPair_radicand : 1 - 2 * X * halfPairV branchZeta = geometricSeries ^ 2 := by
  have hc : (2 : ℂ⟦X⟧) * C (1 / 2 : ℂ) = 1 := by
    rw [← map_ofNat C, ← map_mul]; norm_num
  unfold halfPairV
  have hz : 2 + branchZeta = 1 + geometricSeries := by
    linear_combination one_add_branchZeta
  rw [one_add_branchZeta, hz]
  linear_combination (X * geometricSeries * (1 + geometricSeries)) * hc -
    (1 + geometricSeries) * geometricSeries_mul_one_sub

/--
@isnad1 id=eq.0h0v.s7.510e8281679e from=translated src=- shape=d8ba60ff vocab=cd17fea1
-/
theorem halfPair_radicand_inverse :
    1 - 2 * X * halfPairV branchZeta = ((1 - X : ℂ⟦X⟧)⁻¹) ^ 2 := by
  rw [halfPair_radicand, geometricSeries_eq_inv]

/-- The polynomial h(z)=1+z in the three-variable discovery formula. -/
def halfPairH : Polynomial ℂ := 1 + Polynomial.X

/--
@isnad1 id=eq.0h0v.s7.60c5fb199d29 from=translated src=- shape=3bacb3eb vocab=5f85f3b8
-/
theorem halfPair_denominator :
    1 - X * Polynomial.eval₂ C branchZeta halfPairH.derivative = (1 - X : ℂ⟦X⟧) := by
  simp [halfPairH]

/-- The normalized inverse square root is 1-t: its square times the radicand is one.
@isnad1 id=eq.0h0v.s7.b7dbc598b358 from=translated src=- shape=65fdb1b0 vocab=81a6f6bb
-/
theorem halfPair_inverse_sqrt :
    (1 - X) ^ 2 * (1 - 2 * X * halfPairV branchZeta) = (1 : ℂ⟦X⟧) := by
  rw [halfPair_radicand, ← mul_pow, one_sub_mul_geometricSeries, one_pow]

/-- Constant coefficient one selects the unique inverse square-root branch.
@isnad1 id=eq.2h1v.s7.6cce9da48285 from=translated src=- shape=44dd9527 vocab=59e9dd12
-/
theorem halfPair_inverse_sqrt_unique (s : ℂ⟦X⟧)
    (hs0 : constantCoeff s = 1)
    (hs : s ^ 2 * (1 - 2 * X * halfPairV branchZeta) = 1) : s = 1 - X := by
  have hsq : s ^ 2 = (1 - X) ^ 2 := by
    have hh := congrArg (fun a => a * (1 - X) ^ 2) hs
    rw [halfPair_radicand, mul_assoc, ← mul_pow, geometricSeries_mul_one_sub,
      one_pow, mul_one, one_mul] at hh
    exact hh
  obtain h | h := (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
  · exact h
  · have hc := congrArg constantCoeff h
    norm_num [hs0] at hc

/-- The normalized inverse square-root factor cancels the denominator exactly.
@isnad1 id=eq.0h0v.s6.5168e6835956 from=translated src=- shape=7bace7f8 vocab=59a5cd15
-/
theorem halfPair_cancellation : (1 - X) * geometricSeries = (1 : ℂ⟦X⟧) :=
  one_sub_mul_geometricSeries

end GaussianMomentsCounterexamples
