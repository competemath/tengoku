import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Interlacing
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.MatrixTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lower spectral products and the negative-order conclusion

This file assembles the determinant theorem and the shorting argument into
the main finite-dimensional result.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix

theorem prod_decreasingEigenvalues_eq_prod_increasingEigenvalues
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (∏ i, decreasingEigenvalues hA i) =
      ∏ i, increasingEigenvalues hA i := by
  simpa [increasingEigenvalues, Function.comp_def] using
    (Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n)
      (decreasingEigenvalues hA)).symm

end HiaiLimPowerMeans
