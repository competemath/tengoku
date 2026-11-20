import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Scalar
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.OrderedSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Matrix determinant bridge

Mathlib supplies decreasingly indexed eigenvalues for self-adjoint linear maps,
positivity of the eigenvalues of a positive-definite matrix, and the identity
`det A = product eigenvalues`.  This file converts the normalized scalar trace
bound into the determinant inequality.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder

/-- The determinant consequence of the normalized trace bound.
@isnad1 id=le.4h5v.s8.369949f24ced from=translated src=- shape=da0d4342 vocab=65116927
-/
theorem det_ge_prod_of_normalized_trace_bound
    {n : ℕ} [NeZero n] {𝕜 : Type*} [RCLike 𝕜]
    {Y : Matrix (Fin n) (Fin n) 𝕜} (hY : Y.PosDef)
    {q : Fin n → ℝ} {t : ℝ}
    (hq : ∀ i, 0 < q i) (ht : 0 < t)
    (htrace :
      ∑ i, (q i / decreasingEigenvalues hY.isHermitian i) ^ t ≤ (n : ℝ)) :
    ∏ i, q i ≤ RCLike.re Y.det := by
  have hscalar :
      (∏ i, q i) ≤ ∏ i, decreasingEigenvalues hY.isHermitian i :=
    product_le_product_of_sum_rpow_div_le_card
      hq (Matrix.PosDef.decreasingEigenvalues_pos hY) ht htrace
  calc
    (∏ i, q i) ≤ ∏ i, decreasingEigenvalues hY.isHermitian i := hscalar
    _ = ∏ i, hY.isHermitian.eigenvalues i :=
      prod_comp_decreasingEigenvalues_eq_eigenvalues hY.isHermitian id
    _ = RCLike.re Y.det := by
      have hdet := congrArg RCLike.re hY.isHermitian.det_eq_prod_eigenvalues
      have hre_prod :
          RCLike.re (∏ i, (hY.isHermitian.eigenvalues i : 𝕜)) =
            ∏ i, hY.isHermitian.eigenvalues i := by
        classical
        induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            simp only [Finset.prod_insert hi]
            simp [ih]
      exact hre_prod.symm.trans hdet.symm

end HiaiLimPowerMeans
