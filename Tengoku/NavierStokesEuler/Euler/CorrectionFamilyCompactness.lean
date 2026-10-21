import Tengoku.NavierStokesEuler.Euler.ViscosityCauchy
import Tengoku.NavierStokesEuler.Euler.SobolevCauchyInterpolation
import Tengoku.NavierStokesEuler.Euler.SobolevPathLimits

/-! Tengoku repair: `restrict_eq_truncate` ran out of heartbeats in the tree; `maxHeartbeats` is 1600000 for it (was 200000). -/
/-! Tengoku repair: `exists_limit_with_constraints` ran out of heartbeats in the tree; `maxHeartbeats` is 1600000 for it (was 200000). -/

namespace EulerCorrectionFamilyCompactness
end EulerCorrectionFamilyCompactness
namespace MeasureTheory
end MeasureTheory
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerCorrectionOperators
end EulerCorrectionOperators
namespace EulerQuadraticSource
end EulerQuadraticSource
namespace EulerCorrectionStabilityBudget
end EulerCorrectionStabilityBudget
namespace EulerViscosityCauchy
end EulerViscosityCauchy
namespace EulerSobolevCauchyInterpolation
end EulerSobolevCauchyInterpolation
namespace EulerSobolevPathLimits
end EulerSobolevPathLimits
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Strong lower-Sobolev compactness of an actual uniformly bounded correction family. -/

noncomputable section

namespace EulerCorrectionFamilyCompactness
open _root_.EulerCorrectionFamilyCompactness

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerCorrectionStabilityBudget EulerViscosityCauchy
  EulerSobolevCauchyInterpolation EulerSobolevPathLimits
open _root_.MeasureTheory _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerCorrectionOperators _root_.EulerCorrectionStabilityBudget _root_.EulerViscosityCauchy _root_.EulerSobolevCauchyInterpolation _root_.EulerSobolevPathLimits
open _root_.EulerQuadraticSource hiding Coefficients Coefficients.apply Coefficients.apply_bound Coefficients.apply_sub_bound Coefficients.ballBound Coefficients.ballBound_nonneg Coefficients.ballLipschitz Coefficients.ballLipschitz_nonneg Coefficients.casesOn Coefficients.comp Coefficients.comp_apply Coefficients.continuous Coefficients.ctorIdx Coefficients.forcing Coefficients.linear Coefficients.mk Coefficients.mk.inj Coefficients.mk.injEq Coefficients.mk.noConfusion Coefficients.mk.sizeOf_spec Coefficients.noConfusion Coefficients.noConfusionType Coefficients.projection Coefficients.quadratic Coefficients.rec Coefficients.recOn nestedGroup
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev normed-group instance for family compactness. -/
local instance familySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- The inherited real Sobolev module instance for family compactness. -/
local instance familySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

set_option maxHeartbeats 1600000 in
/-- The actual one-order restriction equals the original truncation map. -/
theorem restrict_eq_truncate (q : ℕ) : restrictOperator period (Nat.le_succ q)=truncateOperator period q := by
  apply ContinuousLinearMap.ext
  intro f
  apply value_injective period
  rfl

set_option maxHeartbeats 1600000 in
/-- Actual strong lower-order Sobolev compactness retains the trace, divergence constraint and common norm bound. -/
theorem exists_limit_with_constraints {s q : ℕ} (hqs : q < s) (T : ℝ) (hT : 0 ≤ T)
    (κ : ℝ) (m : Vector3) (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period s)) (M : ℝ)
    (huM : ∀ n, ‖u n‖ ≤ M) (hu0 : ∀ n, u n ⟨0,le_rfl,hT⟩=0)
    (hud : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period κ m)
    (hCauchy : CauchySeq (fun n => (valueOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))) :
    ∃ e : C(Icc (0 : ℝ) T,SobolevSpace period q),
      Filter.Tendsto (fun n => (restrictOperator period hqs.le).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))
        Filter.atTop (𝓝 e) ∧
      e ⟨0,le_rfl,hT⟩=0 ∧ (∀ t, value period (e t) ∈ divergenceFreeSpace period κ m) ∧ ‖e‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (huM 0)
  obtain ⟨e,hlimit⟩ := exists_limit_restrict_of_value period hqs T M hM u huM hCauchy
  let ul := fun n => (restrictOperator period hqs.le).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n)
  have hul (n : ℕ) : ‖ul n‖ ≤ M := (restrict_path_norm period hqs.le T (u n)).trans (huM n)
  have hi : e ⟨0,le_rfl,hT⟩=0 := limit_zero_trace period T ⟨0,le_rfl,hT⟩ ul e hlimit (fun n => by
    change restrictOperator period hqs.le (u n ⟨0,le_rfl,hT⟩)=0
    rw [hu0 n,map_zero])
  have hd : ∀ t, value period (e t) ∈ divergenceFreeSpace period κ m :=
    limit_divergenceFree period T κ m ul e hlimit hud
  exact ⟨e,hlimit,hi,hd,limit_norm_bound period T M ul e hlimit hul⟩

/-- Genuine uniformly bounded correction solutions with Cauchy viscosities have an actual strong lower-Sobolev limit with the original trace and divergence constraint. -/
theorem exists_correction_family_limit {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n) (hν1 : ∀ n, ν n ≤ 1) (hνc : CauchySeq ν)
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period (q+1))) (M : ℝ) (huM : ∀ n, ‖u n‖ ≤ M)
    (hu0 : ∀ n, u n ⟨0,le_rfl,hT⟩=0)
    (hu : ∀ n t, u n t = quadraticDuhamel period (ν n) (hν n) hT le_rfl (D.coefficients period hq) 0 (u n) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∃ e : C(Icc (0 : ℝ) T,SobolevSpace period q),
      Filter.Tendsto (fun n => (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))
        Filter.atTop (𝓝 e) ∧
      e ⟨0,le_rfl,hT⟩=0 ∧ (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧ ‖e‖ ≤ M := by
  have hCauchy := correction_family_cauchy period hq T hT D B ν hν hν1 hνc u M huM hu hz hud
  have h := exists_limit_with_constraints period (Nat.lt_succ_self q) T hT D.κ D.direction u M huM hu0 hud hCauchy
  simpa only [restrict_eq_truncate period q] using h

end EulerCorrectionFamilyCompactness
