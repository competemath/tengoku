import Tengoku.NavierStokesEuler.Euler.TimeLpLinearity

/-! Actual finite families of continuous and Bochner time fields, with exact norm-topology compatibility. -/

noncomputable section

namespace EulerTimeFamily

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite family of continuous time paths as the actual continuous family-valued path. -/
def familyPath (T : ℝ) (u : I → C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, I → E) :=
  ⟨fun t i => u i t, continuous_pi (fun i => (u i).continuous)⟩

/-- A finite family of actual Bochner fields, constructed by the genuine bounded coordinate injections. -/
def familyTime (T : ℝ) (u : I → TimeLp T E) : TimeLp T (I → E) := by
  classical
  exact ∑ i, (ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure T) (u i)

end EulerTimeFamily
