import Tengoku.SingularityCompleteLean.Singularity.StationaryDensity
import Tengoku.SingularityCompleteLean.Singularity.GreenDistance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The logarithmic cocycle of an actual stationary measure

The inverse in the definition matches the usual Busemann convention:
sigma(gh,x) = sigma(g,hx) + sigma(h,x). The derivatives are those of actual
translated measures. Green bounds follow from optional stopping, without any
identification with a geometric Martin boundary.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]

/-- The real logarithmic Radon–Nikodym cocycle, in the forward-action convention.-/
def stationaryLogCocycle (ν : Measure B) (g : Γ) (ξ : B) : ℝ :=
  -Real.log (stationaryRealDensity ν g⁻¹ ξ)

omit [MeasurableConstSMul Γ B] in
/-- Each group element defines a measurable real boundary function.-/
theorem measurable_stationaryLogCocycle (ν : Measure B) (g : Γ) :
    Measurable (stationaryLogCocycle ν g) :=
  ((measurable_stationaryDensity ν g⁻¹).ennreal_toReal.log).neg

variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (ν : Measure B) [IsFiniteMeasure ν]
  (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)

include hpos hgen hstat in
/-- The real-valued derivatives satisfy the multiplicative cocycle identity.-/
theorem stationaryRealDensity_cocycle (g h : Γ) :
    ∀ᵐ ξ ∂ν, stationaryRealDensity ν (g * h) ξ =
      stationaryRealDensity ν g ξ * stationaryRealDensity ν h (g⁻¹ • ξ) := by
  filter_upwards [stationaryDensity_cocycle s μ hpos hgen ν hstat g h] with ξ hξ
  simpa only [stationaryRealDensity, ENNReal.toReal_mul] using congrArg ENNReal.toReal hξ

omit [MeasurableConstSMul Γ B] in
/-- The logarithmic cocycle is zero at the identity almost everywhere.-/
theorem stationaryLogCocycle_one : stationaryLogCocycle ν (1 : Γ) =ᵐ[ν] fun _ => 0 := by
  filter_upwards [stationaryDensity_one (Γ := Γ) ν] with ξ hξ
  simp only [stationaryLogCocycle, inv_one, stationaryRealDensity, hξ,
    ENNReal.toReal_one, Real.log_one, neg_zero]

end Singularity
