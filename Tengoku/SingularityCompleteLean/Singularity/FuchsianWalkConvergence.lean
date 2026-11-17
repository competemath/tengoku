import Tengoku.SingularityCompleteLean.Singularity.HyperbolicOrbitGrowth
import Tengoku.SingularityCompleteLean.Singularity.SpectralEscape
import Tengoku.SingularityCompleteLean.Singularity.GeometricPathConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full geometric convergence from discreteness and the operator spectral gap

The exponential orbit-count bound and uniform spectral decay imply almost-sure
positive linear escape by Borel--Cantelli. Finite support bounds hyperbolic jumps;
the Cayley estimate then proves full compact convergence. This constructs the
geometric hitting law independently of the Green distance comparison.

The nonamenability-to-spectral-gap criterion remains a separate obligation.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A sufficiently small positive escape rate is dominated by spectral decay.
@isnad1 id=ex.2h1v.s6.95a5a891d21d from=translated src=- shape=3c2ff630 vocab=a1f884aa
-/
theorem exists_positive_escape_rate {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ a : ℝ, 0 < a ∧ Real.exp (4 * a) * q < 1 := by
  have hl : Real.log q < 0 := Real.log_neg hq hq1
  refine ⟨-Real.log q / 8, by linarith, ?_⟩
  have he : Real.exp (4 * (-Real.log q / 8)) * q = Real.exp (Real.log q / 2) := by
    calc
      _ = Real.exp (4 * (-Real.log q / 8)) * Real.exp (Real.log q) := by rw [Real.exp_log hq]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.exp_lt_one_iff.mpr (by linarith)

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]

omit [DiscreteTopology Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] in
/-- Changing the initial point in the half-plane changes radial distance by a bounded amount.
@isnad1 id=le.0h3v.s12.ba16e697493e from=translated src=- shape=6de53ed3 vocab=323ca284
-/
theorem orbit_radial_basepoint_bound (g : Γ) (z : ℍ) :
    dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤
      dist (g • z) UpperHalfPlane.I + dist z UpperHalfPlane.I := by
  have h := dist_triangle (g • UpperHalfPlane.I) (g • z) UpperHalfPlane.I
  change dist (((g : SL(2, ℝ)) • UpperHalfPlane.I)) UpperHalfPlane.I ≤
    dist (((g : SL(2, ℝ)) • UpperHalfPlane.I)) (((g : SL(2, ℝ)) • z)) +
      dist (g • z) UpperHalfPlane.I at h
  rw [dist_smul (g : SL(2, ℝ))] at h
  change dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤
    dist UpperHalfPlane.I z + dist (g • z) UpperHalfPlane.I at h
  simpa only [dist_comm UpperHalfPlane.I z, add_comm] using h

end Singularity
