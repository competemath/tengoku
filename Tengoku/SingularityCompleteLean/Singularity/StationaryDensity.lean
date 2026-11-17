import Tengoku.SingularityCompleteLean.Singularity.StationaryQuasiInvariant
import Tengoku.SingularityCompleteLean.Singularity.ReflectedSupport
import Tengoku.Seed.MeasureTheory.Measure.Decomposition.RadonNikodym
import Tengoku.Seed.MeasureTheory.Group.MeasurableEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Radon–Nikodym densities of stationary boundary translates

The densities here are derivatives of actual pushforward measures, not assumed
Martin kernels. Semigroup generation proves positivity; stationarity proves
their harmonic equation. Identification with geometric Martin limits remains
a separate obligation.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
    [MeasurableConstSMul Γ B]

/-- The extended Radon–Nikodym density of the law viewed from a group element.-/
def stationaryDensity (ν : Measure B) (g : Γ) : B → ℝ≥0∞ :=
  (Measure.map (fun ξ : B => g • ξ) ν).rnDeriv ν

omit [MeasurableConstSMul Γ B] in
theorem measurable_stationaryDensity (ν : Measure B) (g : Γ) :
    Measurable (stationaryDensity ν g) := Measure.measurable_rnDeriv _ _

variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (ν : Measure B) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)

include hpos hgen hstat in
/-- The stationary density reconstructs the actual translated law.-/
theorem stationaryDensity_withDensity (g : Γ) :
    ν.withDensity (stationaryDensity ν g) = Measure.map (fun ξ : B => g • ξ) ν :=
  Measure.withDensity_rnDeriv_eq _ _ (stationary_translate_equivalent s μ hpos hgen ν hstat g).1

include hpos hgen hstat in
/-- Each translate has a positive finite density almost everywhere.-/
theorem stationaryDensity_positive_finite (g : Γ) :
    ∀ᵐ ξ ∂ν, 0 < stationaryDensity ν g ξ ∧ stationaryDensity ν g ξ < ∞ := by
  exact (Measure.rnDeriv_pos' (stationary_translate_equivalent s μ hpos hgen ν hstat g).2).and
    (Measure.rnDeriv_lt_top _ _)

omit [MeasurableConstSMul Γ B] in
/-- The density is normalized at the identity.-/
theorem stationaryDensity_one : stationaryDensity ν (1 : Γ) =ᵐ[ν] fun _ => 1 := by
  unfold stationaryDensity
  have he : (fun ξ : B => (1 : Γ) • ξ) = id := by funext ξ; exact one_smul Γ ξ
  rw [he, Measure.map_id]
  exact Measure.rnDeriv_self ν

/-- The real-valued derivative used by the harmonic-function and Martin modules.-/
def stationaryRealDensity (ν : Measure B) (g : Γ) (ξ : B) : ℝ :=
  (stationaryDensity ν g ξ).toReal

include hpos hgen hstat in
/-- Derivatives of actual translates satisfy the Radon–Nikodym cocycle identity.-/
theorem stationaryDensity_cocycle (g h : Γ) :
    ∀ᵐ ξ ∂ν, stationaryDensity ν (g * h) ξ =
      stationaryDensity ν g ξ * stationaryDensity ν h (g⁻¹ • ξ) := by
  have hcomp : Measure.map (fun ξ : B => g • ξ) (Measure.map (fun ξ : B => h • ξ) ν) =
      Measure.map (fun ξ : B => (g * h) • ξ) ν := by
    rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
    congr 1
    funext ξ
    exact (mul_smul g h ξ).symm
  have hm := (measurableEmbedding_const_smul (α := B) g).rnDeriv_map
    (Measure.map (fun ξ : B => h • ξ) ν) ν
  rw [hcomp] at hm
  have hq : Measure.QuasiMeasurePreserving (fun ξ : B => g⁻¹ • ξ) ν ν :=
    ⟨measurable_const_smul g⁻¹, (stationary_translate_equivalent s μ hpos hgen ν hstat g⁻¹).1⟩
  have hac : Measure.map (fun ξ : B => (g * h) • ξ) ν ≪
      Measure.map (fun ξ : B => g • ξ) ν := by
    rw [← hcomp]
    exact ((stationary_translate_equivalent s μ hpos hgen ν hstat h).1).map
      (measurable_const_smul g)
  have hc := Measure.rnDeriv_mul_rnDeriv (κ := ν) hac
  filter_upwards [hq.ae hm, hc] with ξ hm hc
  simp only [smul_inv_smul] at hm
  change _ * stationaryDensity ν g ξ = stationaryDensity ν (g * h) ξ at hc
  rw [hm] at hc
  exact hc.symm.trans (mul_comm _ _)

end Singularity
