import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.FullPolarization
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
import Tengoku.Seed.LinearAlgebra.Quotient.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Grouped coefficients of a multilinear map on `K^d`

For a multilinear map `p` on `Fin d → K`, the grouped coefficient of a multi-index `α`
(the sum of `p` over all basis selections of type `α`) lies in any subspace containing
the diagonal values of `p`, and is bounded by the number of terms times `‖p‖`. Used for
the coefficient bounds of Theorem 4.4.
-/

noncomputable section

namespace FiniteCoordinateReflection

variable {K Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z] {d n : ℕ}

/-- A grouped coefficient has norm at most `‖p‖` times its number of terms.-/
theorem norm_sumOfType_le
    (p : (Fin d → K) [×n]→L[K] Z) (α : Fin d → ℕ) :
    ‖p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) α‖ ≤
      ∑ _f ∈ Finset.univ.filter
        (fun f : Fin n → Fin d => Polarization.selectionType f = α), ‖p‖ := by
  classical
  unfold MultilinearMap.sumOfType
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro f hf
  apply p.unit_le_opNorm
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases h : j = f i <;> simp [h]

end FiniteCoordinateReflection
