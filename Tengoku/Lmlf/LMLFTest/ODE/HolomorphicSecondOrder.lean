import Tengoku.Lmlf.LMLF.ODE.HolomorphicSecondOrder
import Tengoku.Lmlf.LMLF.ODE.Hypergeometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace LMLFTest.ODE

open Filter LMLF.Definitions Metric Set
open scoped Topology

-- The scalar theorem exposes a genuine `HasDerivAt (deriv w)` equation.

/-- The generic scalar IVP theorem is genuinely reusable by the accepted regularized Gauss series
on every simply connected subdomain where the normalized coefficients are nonsingular.-/
theorem regularizedGauss_reuses_holomorphicSecondOrderLinearIVP
    (a b c : ℂ) {Z : Set ℂ} (hZ : IsOpen Z) (hZc : IsSimplyConnected Z)
    (hZball : Z ⊆ ball 0 1) (h0Z : 0 ∉ Z) {x₀ : ℂ} (hx₀ : x₀ ∈ Z) :
    let R := regularizedGaussHypergeometricSeriesSum a b c
    let f : ℂ → ℂ := fun z ↦ (c - (a + b + 1) * z) / (z * (1 - z))
    let g : ℂ → ℂ := fun z ↦ -(a * b) / (z * (1 - z))
    ∃ w : ℂ → ℂ, AnalyticOnNhd ℂ w Z ∧ w x₀ = R x₀ ∧
      HasDerivAt w (deriv R x₀) x₀ ∧
      (∀ z ∈ Z, HasDerivAt (deriv w) (-(f z * deriv w z + g z * w z)) z) ∧
      EqOn w R Z := by
  dsimp only
  let R := regularizedGaussHypergeometricSeriesSum a b c
  let d : ℂ → ℂ := fun z ↦ z * (1 - z)
  let N : ℂ → ℂ := fun z ↦ c - (a + b + 1) * z
  let f : ℂ → ℂ := fun z ↦ N z / d z
  let g : ℂ → ℂ := fun z ↦ -(a * b) / d z
  have hd : ∀ z ∈ Z, d z ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := fun h ↦ h0Z (h ▸ hz)
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      have hone : ‖(1 : ℂ)‖ < 1 := by
        simpa [mem_ball] using hZball hz
      norm_num at hone
    exact mul_ne_zero hz0 (sub_ne_zero.mpr hz1.symm)
  have hdAnalytic : AnalyticOnNhd ℂ d Z := by
    simpa [d] using (analyticOnNhd_id.mul
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (1 : ℂ)) Z).sub analyticOnNhd_id))
  have hNAnalytic : AnalyticOnNhd ℂ N Z := by
    have h := (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ c) Z).sub
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ a + b + 1) Z).mul
        analyticOnNhd_id)
    exact AnalyticOnNhd.congr hZ h fun _ _ ↦ rfl
  have hf : AnalyticOnNhd ℂ f Z := hNAnalytic.div hdAnalytic hd
  have hg : AnalyticOnNhd ℂ g Z := by
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ ↦ -(a * b)) Z := analyticOnNhd_const
    exact hconst.div hdAnalytic hd
  have hRAnalytic : AnalyticOnNhd ℂ R Z :=
    (regularizedGaussHypergeometricSeriesSum_analyticOnNhd a b c).mono hZball
  have hROde : ∀ z ∈ Z,
      HasDerivAt (deriv R) (-(f z * deriv R z + g z * R z)) z := by
    intro z hz
    have hnorm : ‖z‖ < 1 := by simpa [mem_ball] using hZball hz
    have hGauss := LMLF.ODE.regularizedGaussHypergeometricSeriesSum_gaussEquation
      (a := a) (b := b) (c := c) hnorm
    have hnormalized : deriv (deriv R) z = -(f z * deriv R z + g z * R z) := by
      have hdiv : deriv (deriv R) z =
          (-(N z * deriv R z) + a * b * R z) / d z := by
        apply (eq_div_iff (hd z hz)).2
        dsimp only [R, N, d]
        linear_combination hGauss
      rw [hdiv]
      dsimp only [f, g]
      field_simp [hd z hz]
      ring
    exact (hRAnalytic.deriv z hz).differentiableAt.hasDerivAt.congr_deriv hnormalized
  have hRInitial : HasDerivAt R (deriv R x₀) x₀ :=
    (hRAnalytic x₀ hx₀).differentiableAt.hasDerivAt
  obtain ⟨w, hwAnalytic, hw0, hw1, hwOde, hwUnique⟩ :=
    LMLF.ODE.exists_unique_holomorphicSecondOrderLinear
      hZ hZc hf hg hx₀ (R x₀) (deriv R x₀)
  exact ⟨w, hwAnalytic, hw0, hw1, hwOde,
    hwUnique R hRAnalytic rfl hRInitial hROde⟩

end LMLFTest.ODE
