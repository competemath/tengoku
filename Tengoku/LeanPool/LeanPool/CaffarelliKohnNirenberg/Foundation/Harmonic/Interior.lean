/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku.Seed.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interior

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section

namespace CKN.Foundation.Heat

/--
@isnad1 id=eq.2h5v.s6.3c6e9cf570ec from=translated src=- shape=d91cee5c vocab=9d1d4eee
-/
theorem spatialDeriv_kernelCutoffDerivative_at_x
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) j x = 0 := by
  have heq : kernelCutoffDerivative x x₀ hρ i =ᶠ[𝓝 x]
      (fun _ : Vec3 => (0 : ℝ)) := by
    exact spatialDeriv_eta_eventually_zero x x₀ hρ hx i |>.mono fun z hz => by
      simp [kernelCutoffDerivative, hz]
  have hfd := heq.fderiv_eq (𝕜 := ℝ)
  change (fderiv ℝ (kernelCutoffDerivative x x₀ hρ i) x)
      (CKN.basisVec j) = 0
  rw [hfd]
  simp

/--
@isnad1 id=contdiff.2h4v.s7.547e448b8e24 from=translated src=- shape=ee20114e vocab=42abcd7d
-/
theorem kernelCutoffDerivative_contDiff_one (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) := by
  exact kernelCutoffDerivative_contDiff x x₀ hρ hx i

/--
@isnad1 id=hascompa.1h4v.s5.cd938c07436d from=translated src=- shape=2140d6c5 vocab=9fee0d53
-/
theorem kernelCutoffDerivative_hasCompactSupport_global (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) := by
  exact kernelCutoffDerivative_hasCompactSupport x x₀ hρ i

/--
@isnad1 id=integrab.3h5v.s8.11426b27ac68 from=translated src=- shape=c9940616 vocab=1c8a84b3
-/
theorem kernelCutoffDerivative_integrable_mul_right_global
    {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y)
      volume := by
  exact kernelCutoffDerivative_integrable_mul_right hh x x₀ hρ hx i

/--
@isnad1 id=contdiff.1h3v.s7.76e29b38ef2f from=translated src=- shape=5ab5a58d vocab=57f98e19
-/
theorem eta_spatialDeriv_contDiff_two_global (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    ContDiff ℝ (2 : ℕ) (spatialDeriv (eta x₀ hρ) i) := by
  exact contDiff_spatialDeriv_two
    (by simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ) i

/--
@isnad1 id=continuo.1h3v.s6.cf466f9f298b from=translated src=- shape=a2bb859c vocab=7aceccfe
-/
theorem eta_spatialSecond_continuous_global (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    Continuous (spatialDeriv (spatialDeriv (eta x₀ hρ) i) i) := by
  exact (eta_spatialDeriv_contDiff_two_global x₀ hρ i).continuous_fderiv
    (by norm_num) |>.clm_apply continuous_const

end CKN.Foundation.Heat
