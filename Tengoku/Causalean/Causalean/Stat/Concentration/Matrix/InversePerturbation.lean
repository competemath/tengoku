/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.NormedSpace.InversePerturbation

/-!
# Entrywise perturbation of the inverse design moment matrix

Deterministic inverse-perturbation bounds that transport entrywise matrix deviations into control
of a design inverse.

The interior local-polynomial variance rate `(M⁻¹)₀₀ = O(1/(Nh))` is obtained by transporting
an *entrywise* concentration bound on the random design moment matrix `M` (each entry close to
the corresponding entry of a fixed, invertible population matrix `S`) through the matrix
inverse. This file develops the deterministic perturbation step:

if every entry of `M` is within `η` of the corresponding entry of an invertible matrix `S`, and
the rows of `S⁻¹` have absolute sums bounded by `c`, with `c·(p+1)·η ≤ 1/2`, then `M` is
invertible and

`|(M⁻¹)₀₀ − (S⁻¹)₀₀| ≤ 2 c² (p+1) η`.

The argument is the operator (`ℓ∞`-operator, i.e. max-row-sum) norm Neumann/resolvent bound:
`M = S(1 − u)` with `u = S⁻¹(S − M)`, `‖u‖ ≤ ‖S⁻¹‖·‖S − M‖ ≤ 1/2`, so `1 − u` is a unit
(`Units.oneSub`) with `‖(1−u)⁻¹‖ ≤ (1−‖u‖)⁻¹ ≤ 2` (geometric series), hence `M` is a unit with
`‖M⁻¹‖ ≤ 2‖S⁻¹‖`, and the resolvent identity `M⁻¹ − S⁻¹ = M⁻¹(S − M)S⁻¹`
(`norm_unitInv_sub_unitInv_le`) gives `‖M⁻¹ − S⁻¹‖ ≤ 2‖S⁻¹‖²‖S − M‖`. The entry bound follows
since each entry is dominated by the operator norm. The public statement carries only entrywise
hypotheses, so it composes with the iid Chebyshev union bound (for `M` close to `𝔼 M = S`) and
the population positive-definiteness (`designMatrix_posDef`) without exposing the matrix norm.
-/

public section

open Causalean.Mathlib.Analysis.InversePerturbation

namespace Causalean.Stat.Concentration

open scoped BigOperators
open Matrix

section LinftyOp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

variable {p : ℕ}

/-- Completeness of finite matrices under the `ℓ∞`-operator norm follows from the coordinatewise
function-space uniformity. Needed to invoke the Neumann/geometric-series unit API. -/
theorem completeSpace_matrix_linftyOp {α β R : Type*}
    [Fintype α] [Fintype β] [NormedAddCommGroup R] [CompleteSpace R] :
    CompleteSpace (Matrix α β R) :=
  inferInstanceAs (CompleteSpace (α → β → R))

/-- Each coefficient norm is dominated by the `ℓ∞`-operator (max-row-sum) norm. -/
theorem linftyOp_abs_entry_le {α β R : Type*}
    [Fintype α] [Fintype β] [NormedAddCommGroup R]
    (A : Matrix α β R) (i : α) (j : β) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hrow : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k => ‖A i k‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have hsup : (∑ k, ‖A i k‖₊) ≤
      Finset.univ.sup (fun i => ∑ k, ‖A i k‖₊) :=
    Finset.le_sup (s := Finset.univ) (f := fun i => ∑ k, ‖A i k‖₊)
      (Finset.mem_univ i)
  exact_mod_cast le_trans hrow hsup

/-- A row-sum upper bound for the `ℓ∞`-operator norm: if every row's coefficient-norm sum is
`≤ c`, then `‖A‖ ≤ c`. -/
theorem linftyOp_norm_le_of_rowsum {α β R : Type*}
    [Fintype α] [Fintype β] [NormedAddCommGroup R]
    {A : Matrix α β R} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, (∑ j, ‖A i j‖) ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le ?_
    intro i _
    exact NNReal.coe_le_coe.mp (by
      rw [NNReal.coe_sum, Real.coe_toNNReal c hc]
      simpa using h i)
  calc
    ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (c.toNNReal : ℝ) :=
      NNReal.coe_le_coe.mpr hsup
    _ = c := Real.coe_toNNReal c hc

/-- The `ℓ∞`-operator norm of an entrywise-`η`-bounded rectangular matrix is at most its
number of columns times `η`. -/
theorem linftyOp_norm_le_of_entry {q : ℕ}
    {A : Matrix (Fin (p + 1)) (Fin (q + 1)) ℝ} {η : ℝ}
    (h : ∀ i j, |A i j| ≤ η) : ‖A‖ ≤ (q + 1 : ℕ) * η := by
  have hη : 0 ≤ η := le_trans (abs_nonneg (A 0 0)) (h 0 0)
  apply linftyOp_norm_le_of_rowsum (mul_nonneg (by positivity) hη)
  intro i
  calc
    ∑ j, |A i j| ≤ ∑ _j : Fin (q + 1), η :=
      Finset.sum_le_sum (fun j _ => h i j)
    _ = (q + 1 : ℕ) * η := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end LinftyOp

end Causalean.Stat.Concentration
