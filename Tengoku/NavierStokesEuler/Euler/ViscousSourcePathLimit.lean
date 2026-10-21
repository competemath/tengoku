import Tengoku.NavierStokesEuler.Euler.QuadraticSourceLimit
import Tengoku.NavierStokesEuler.Euler.SobolevPathLimits
import Tengoku.NavierStokesEuler.Euler.ViscosityDefect

/-! Tengoku repair: `viscousSourcePath_tendsto` ran out of heartbeats in the tree; `maxHeartbeats` is 1600000 for it (was 200000). -/

namespace EulerViscousSourcePathLimit
end EulerViscousSourcePathLimit
namespace Set
end Set
namespace EulerLiftedGradientSpace
end EulerLiftedGradientSpace
namespace EulerCylinderSobolevSpace
end EulerCylinderSobolevSpace
namespace EulerCylinderSobolev
end EulerCylinderSobolev
namespace EulerQuadraticSource
end EulerQuadraticSource
namespace EulerQuadraticSourceLimit
end EulerQuadraticSourceLimit
namespace EulerSobolevPathLimits
end EulerSobolevPathLimits
namespace EulerViscosityDefect
end EulerViscosityDefect
namespace EulerViscosityCauchy
end EulerViscosityCauchy
namespace Topology
end Topology

namespace NavierStokesEulerFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Strong convergence of the actual nonlinear and viscous right-hand sides. -/

noncomputable section

namespace EulerViscousSourcePathLimit
open _root_.EulerViscousSourcePathLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerQuadraticSource EulerQuadraticSourceLimit EulerSobolevPathLimits
  EulerViscosityDefect EulerViscosityCauchy
open _root_.Set _root_.EulerLiftedGradientSpace _root_.EulerCylinderSobolevSpace _root_.EulerCylinderSobolev _root_.EulerQuadraticSourceLimit _root_.EulerSobolevPathLimits _root_.EulerViscosityDefect _root_.EulerViscosityCauchy
open _root_.EulerQuadraticSource hiding Coefficients Coefficients.apply Coefficients.apply_bound Coefficients.apply_sub_bound Coefficients.ballBound Coefficients.ballBound_nonneg Coefficients.ballLipschitz Coefficients.ballLipschitz_nonneg Coefficients.casesOn Coefficients.comp Coefficients.comp_apply Coefficients.continuous Coefficients.ctorIdx Coefficients.forcing Coefficients.linear Coefficients.mk Coefficients.mk.inj Coefficients.mk.injEq Coefficients.mk.noConfusion Coefficients.mk.sizeOf_spec Coefficients.noConfusion Coefficients.noConfusionType Coefficients.projection Coefficients.quadratic Coefficients.rec Coefficients.recOn nestedGroup
open scoped Topology _root_.Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group on each actual Sobolev value space. -/
local instance sourceLimitGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) := inferInstance

/-- The inherited real normed space on each actual Sobolev value space. -/
local instance sourceLimitSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance

/-- The literal continuous viscous right-hand side with the source evaluated one Sobolev order lower. -/
def viscousSourcePath {q : ℕ} (hq : 2 ≤ (q+1)+1) (ν T : ℝ)
    (C : Coefficients (Icc (0 : ℝ) T) (SobolevSpace period (q+1)) (SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T,SobolevSpace period ((q+1)+1))) :
    C(Icc (0 : ℝ) T,LiftL2 period) :=
  viscousDefect period hq ν T u + valuePath period T
    (sourcePath C ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u))

set_option maxHeartbeats 1600000 in
/-- Uniformly bounded strongly convergent states have convergent actual nonlinear-viscous right-hand sides. -/
theorem viscousSourcePath_tendsto {q : ℕ} (hq : 2 ≤ (q+1)+1) (T : ℝ)
    (C : Coefficients (Icc (0 : ℝ) T) (SobolevSpace period (q+1)) (SobolevSpace period q))
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period ((q+1)+1)))
    (e : C(Icc (0 : ℝ) T,SobolevSpace period (q+1))) (M : ℝ) (huM : ∀ n, ‖u n‖ ≤ M)
    (hconv : Filter.Tendsto (fun n => (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))
      Filter.atTop (𝓝 e)) :
    Filter.Tendsto (fun n => viscousSourcePath period hq (viscositySequence n) T C (u n))
      Filter.atTop (𝓝 (valuePath period T (sourcePath C e))) := by
  let v := fun n => (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n)
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (huM 0)
  have hvM : ∀ n, ‖v n‖ ≤ M := fun n =>
    (restrict_path_norm period (by omega : q+1 ≤ (q+1)+1) T (u n)).trans (huM n)
  have heM : ‖e‖ ≤ M := limit_norm_bound period T M v e hconv hvM
  have hg := sourcePath_tendsto C M hM v e hvM heM hconv
  have hgval := ((valueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T)).continuous.tendsto
    (sourcePath C e) |>.comp hg
  have hv := viscousDefect_tendsto_zero period hq T M u huM
  simpa only [viscousSourcePath,v,valuePath,Function.comp_def,zero_add] using hv.add hgval

/-- Strong convergence after restriction preserves the underlying continuous L² path. -/
theorem valuePath_tendsto_of_truncate {q : ℕ} (T : ℝ)
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period (q+1)))
    (e : C(Icc (0 : ℝ) T,SobolevSpace period q))
    (hconv : Filter.Tendsto (fun n => (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))
      Filter.atTop (𝓝 e)) :
    Filter.Tendsto (fun n => valuePath period T (u n)) Filter.atTop (𝓝 (valuePath period T e)) :=
  ((valueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T)).continuous.tendsto e |>.comp hconv

end EulerViscousSourcePathLimit
