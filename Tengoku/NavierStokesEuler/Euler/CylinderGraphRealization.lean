import Tengoku.NavierStokesEuler.Euler.CylinderPathWords
import Tengoku.NavierStokesEuler.Euler.LpBochnerRealization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual spatial L² restrictions of smooth cylinder fields. The bound is
uniform over every continuous phase graph, including arbitrarily high
oscillation frequencies. -/

noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLpBochnerRealization
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]

private theorem norm_sq_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : Lp Vector3 2 μ) (f : X → Vector3)
    (hu : (u : X → Vector3) =ᵐ[μ] f) :
    ‖u‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (hu.mono (fun _ hx =>
    congrArg (fun z : Vector3 => ‖z‖^2) hx))

variable (f : LiftDomain P → Vector3)
  (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x))
  (u v : LiftL2 P)
  (hu : (u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
  (hv : (v : LiftDomain P → Vector3) =ᵐ[liftMeasure P] fieldDerivative P (0,1) f)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

include hf hu hv hθ in
/--
@isnad1 id=memlp.4h5v.s12.b4c71051408d from=translated src=- shape=43333ade vocab=c0822ec1
-/
theorem graph_memLp_of_representatives :
    MemLp (fun x => f (x,θ x)) 2 volume :=
  (graph_memLp_and_energy_bound P f hf
    ((memLp_congr_ae hu).1 (Lp.memLp u))
    ((memLp_congr_ae hv).1 (Lp.memLp v)) θ hθ).1

/-- The actual L² class of the field on the prescribed phase graph. -/
def graphRealization : Lp Vector3 2 (volume : Measure Vector3) :=
  (graph_memLp_of_representatives P f hf u v hu hv θ hθ).toLp (fun x => f (x,θ x))

/--
@isnad1 id=eventual.4h5v.s13.2f3ded778805 from=translated src=- shape=185864d1 vocab=8e83253a
-/
theorem graphRealization_ae :
    (graphRealization P f hf u v hu hv θ hθ : Vector3 → Vector3) =ᵐ[volume]
      fun x => f (x,θ x) :=
  (graph_memLp_of_representatives P f hf u v hu hv θ hθ).coeFn_toLp

include hf hu hv hθ in
/-- Any L² representative of this same graph satisfies the genuine trace bound.
@isnad1 id=le.5h6v.s14.1659404ae713 from=translated src=- shape=78acc9f3 vocab=b61ebd39
-/
theorem graph_norm_sq_le (w : Lp Vector3 2 (volume : Measure Vector3))
    (hw : (w : Vector3 → Vector3) =ᵐ[volume] fun x => f (x,θ x)) :
    ‖w‖^2 ≤ (2/P)*‖u‖^2+(2*P)*‖v‖^2 := by
  rw [norm_sq_of_ae volume w _ hw,
    norm_sq_of_ae (liftMeasure P) u f hu,
    norm_sq_of_ae (liftMeasure P) v _ hv]
  exact (graph_memLp_and_energy_bound P f hf
    ((memLp_congr_ae hu).1 (Lp.memLp u))
    ((memLp_congr_ae hv).1 (Lp.memLp v)) θ hθ).2

/--
@isnad1 id=le.4h5v.s13.92e93ae9e7c8 from=translated src=- shape=559275df vocab=7fa59c54
-/
theorem graphRealization_norm_sq_le :
    ‖graphRealization P f hf u v hu hv θ hθ‖^2 ≤
      (2/P)*‖u‖^2+(2*P)*‖v‖^2 :=
  graph_norm_sq_le P f hf u v hu hv θ hθ _
    (graphRealization_ae P f hf u v hu hv θ hθ)

end EulerCylinderGraphTrace
