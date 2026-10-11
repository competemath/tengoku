import Tengoku.NavierStokesEuler.Euler.CylinderSobolevOperators

/-! Actual coordinate derivatives and truncations between the complete cylinder Sobolev spaces. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

/-- An old word viewed in the next Sobolev order. -/
def truncateIndex {q : ℕ} (w : SobolevWord q) : SobolevWord (q + 1) :=
  ⟨⟨w.1.val, Nat.lt_succ_of_lt w.1.isLt⟩, w.2⟩

/-- Appending a direction indexes a derivative of the corresponding underlying derivative field. -/
def derivativeIndex {q : ℕ} (i : Fin 4) (w : SobolevWord q) : SobolevWord (q + 1) :=
  ⟨⟨w.1.val + 1, Nat.succ_lt_succ w.1.isLt⟩, Fin.snoc w.2 i⟩

variable (period : ℝ) [Fact (0 < period)]

/-- Continuous truncation forgets the highest derivative level. -/
def truncateOperator (q : ℕ) : SobolevSpace period (q + 1) →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q =>
    ContinuousLinearMap.proj (truncateIndex w))).comp (arrayOperator period (q + 1))).codRestrict
    (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      exact word_hasDerivAt period u (Nat.lt_succ_of_lt e.1.isLt) e.2.1 e.2.2)

/-- A coordinate derivative is a bounded map from H^(q+1) to H^q. -/
def derivativeOperator (q : ℕ) (i : Fin 4) :
    SobolevSpace period (q + 1) →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q =>
    ContinuousLinearMap.proj (derivativeIndex i w))).comp (arrayOperator period (q + 1))).codRestrict
    (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      have hd := word_hasDerivAt period u (Nat.succ_lt_succ e.1.isLt) (Fin.snoc e.2.1 i) e.2.2
      change HasDerivAt (fun t => translation period
        (translationPath period (standardDirection e.2.2) t)
        (u.val (derivativeIndex i (edgeParent e))))
        (u.val (derivativeIndex i (edgeChild e))) 0
      simpa only [word, derivativeIndex, edgeParent, edgeChild, Fin.cons_snoc_eq_snoc_cons] using hd)

/-- Truncation is contractive in the complete derivative-array norm. -/
theorem truncateOperator_bound {q : ℕ} (u : SobolevSpace period (q + 1)) :
    ‖truncateOperator period q u‖ ≤ ‖u‖ := by
  change ‖(truncateOperator period q u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro w
  exact word_norm_le period u (truncateIndex w)

end EulerCylinderSobolevSpace
