import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SpherePathChain
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.RadiusProjection
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CommonRadius
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact common-radius finiteness argument for the actual restricted
scalar differential, conditional on the still-open geometric inputs. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Filter
open scoped Topology

/-- An asymptotic sequence gives arbitrarily large radii with the exact
small-gradient and target-distance constraints.-/
theorem radiusApproximationSet_unbounded_of_asymptotic {d : ℕ} (p : AmbientPolynomial d)
    (g : Fin d → AmbientPolynomial d) {c : ℂ}
    (hc : c ∈ asymptoticCriticalValues (fun x : affineTorus d => ambientEval p x.val)
      (fun x => ‖x.val‖) (fun x => ambientDifferentialNorm g x.val))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ B : ℝ, ∃ R ∈ radiusApproximationSet p g c ε δ, B ≤ R := by
  obtain ⟨x, hr, hf, hg⟩ := hc
  intro B
  have hb := hr.eventually (eventually_ge_atTop (max B 2))
  have hsmall := hg.eventually (gt_mem_nhds hε)
  have hclose := (Metric.tendsto_nhds.mp hf) δ hδ
  obtain ⟨n, hn, hs, hd⟩ := (hb.and (hsmall.and hclose)).exists
  refine ⟨‖(x n).val‖, ⟨?_, (x n).val, (x n).property, rfl, hs.le, hd⟩,
    (le_max_left B 2).trans hn⟩
  linarith [le_max_right B 2]

/-- Normalization uses the full induced ambient norm.-/
theorem normalize_mem_smallGradientSphere {d : ℕ} (g : Fin d → AmbientPolynomial d)
    {x : TorusAmbient d} {R ε : ℝ} (hR : 0 < R) (hx : x ∈ affineTorus d)
    (hn : ‖x‖ = R) (hg : R * ambientDifferentialNorm g x ≤ ε) :
    R⁻¹ • x ∈ smallGradientSphere g R ε := by
  have hu : R • R⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  refine ⟨?_, by simpa only [hu] using hx, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hn, inv_mul_cancel₀ hR.ne']
  · simpa only [hu] using hg

end
end DuistermaatVanDerKallen
