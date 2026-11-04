import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Jacobian
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.LocalHomeomorph
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Orientation
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Oriented local charts for the tail-height map

This file supplies the analytic input isolated by `Orientation.lean`.  The
tail heights have the height-Jacobian with row zero deleted.  Coherent signs
make this square differential invertible; the inverse function theorem then
gives a chart.  Cramer's rule identifies every partial derivative of the
omitted height with the strictly negative coefficient recorded in
`heightZeroCramerCoefficient`.  Integrating those derivatives along a line
segment in a convex target proves the required strict order reversal.
-/

namespace Erdos1153.DeBoorPinkus

open Filter Function Topology
open scoped BigOperators Matrix

noncomputable section

/-! ## The tail-height differential -/

/-- The differential of the ambient tail-height representative.-/
def tailHeightDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

/-! ## The deleted-row Cramer identity -/

private lemma updateRow_tailMatrix_eq_permuted_deletedRow
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    (H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0) =
      (H.submatrix k.succ.succAbove id).submatrix k.cycleRange id := by
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  ext i j
  by_cases hik : i = k
  · subst i
    simp
  · by_cases hil : i < k
    · rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_lt hil]
      rw [Fin.succAbove_succ_of_le k (i + 1) (by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one_of_lt' (by omega)]
        omega)]
      apply congrArg (fun q => H q j)
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_succ,
        Fin.val_add_one_of_lt' (by omega)]
    · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hil) (Ne.symm hik)
      rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_gt hki]
      rw [Fin.succAbove_succ_of_lt k i hki]

/-- Replacing row `k` of the tail matrix by row zero is the deleted-`k+1`
minor, with exactly the row-cycle sign used in source equation (8).
@isnad1 id=eq.0h3v.s7.54d49cd01acb from=translated src=- shape=f18295c2 vocab=8ea17056
-/
theorem det_updateRow_tailMatrix
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    ((H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0)).det =
      (-1 : ℝ) ^ (k.val + 2) * deletedRowMinor H k.succ := by
  rw [updateRow_tailMatrix_eq_permuted_deletedRow H k, Matrix.det_permute]
  simp only [Fin.sign_cycleRange, deletedRowMinor]
  norm_num [pow_add]

/-! ## Cramer's rule for the omitted height -/

/-- The differential of height zero at an ordered coordinate vector.-/
def heightZeroDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  (concreteGapCoordinateDerivativesAt hAB u (0 : Fin (d + 1))).valueDifferential.comp
    (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

/-! ## The genuine tail map on the open simplex -/

/-- Tail gap heights in the interior-coordinate chart.-/
def coordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => tailGapHeight (endpointArrayOfInterior hAB v)

/-! ## Differential of height zero through an ambient inverse chart -/

/-! ## The inverse-function chart and its simplex restriction -/

/-! ## Integrating the negative Cramer partials -/

/-! ## Assembly of the canonical oriented chart -/

end

end Erdos1153.DeBoorPinkus
