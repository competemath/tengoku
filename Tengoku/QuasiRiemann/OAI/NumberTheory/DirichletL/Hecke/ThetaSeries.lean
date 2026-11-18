import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Hecke.Theta
import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.LatticeSummability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability

/--
@isnad1 id=eq.0h2v.s5.03163f51902c from=translated src=- shape=0a8fa396 vocab=e8b426e7
-/
@[simp] theorem periodicCoeff_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    periodicCoeff w (0, 0) = w (0, 0) := by
  simp [periodicCoeff, residueEquiv, regroup, Int.divModEquiv, Int.natMod]

/--
@isnad1 id=le.0h3v.s6.e20cbe3142a9 from=translated src=- shape=8d9f9e6a vocab=e43b8c5d
-/
theorem norm_periodicCoeff_le {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (n : ℤ × ℤ) : ‖periodicCoeff w n‖ ≤ ∑ a, ‖w a‖ := by
  unfold periodicCoeff
  exact Finset.single_le_sum (fun a _ => norm_nonneg (w a)) (Finset.mem_univ _)

end SevenEighths.HeckeTheta

end

end OAI
