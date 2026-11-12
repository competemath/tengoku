import Tengoku.AbelFormalization.AbelFormalization.ContourFunctional
import Tengoku.Seed.Analysis.Complex.CauchyIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Analytic families with values in continuous functions on a circle

A jointly continuous family of scalar holomorphic functions on a compact
circle gives an analytic map into the Banach space of continuous circle
functions. The proof uses a Banach-valued Cauchy integral and verifies its
representation by applying continuous evaluation functionals.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace AbelFormalization

/-- A family restricted to a circle, with zero as the default at parameters
where the restriction is not continuous.-/
def contourFamily (F : ℂ × ℂ → ℂ) (R : ℝ) (u : ℂ) : C(sphere (0 : ℂ) R, ℂ) :=
  ContinuousMap.mkD (fun ζ => F (u, ζ)) 0

/-- On its continuous parameter domain, the bundled family has the original
pointwise values.-/
theorem contourFamily_apply {F : ℂ × ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hF : ContinuousOn F (U ×ˢ sphere (0 : ℂ) R)) {u : ℂ} (hu : u ∈ U)
    (ζ : sphere (0 : ℂ) R) : contourFamily F R u ζ = F (u, ζ) := by
  apply ContinuousMap.mkD_apply_of_continuous
  exact hF.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    (fun ζ => ⟨hu, ζ.property⟩)

/-- Joint continuity gives continuity in the uniform norm on the compact
circle.-/
theorem continuousOn_contourFamily {F : ℂ × ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hF : ContinuousOn F (U ×ˢ sphere (0 : ℂ) R)) :
    ContinuousOn (contourFamily F R) U := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hc : ContinuousOn (fun v : ℂ × sphere (0 : ℂ) R => F (v.1, v.2))
      (U ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun v hv => ⟨hv.1, v.2.property⟩)
  apply hc.congr
  intro v hv
  exact contourFamily_apply hF hv.1 v.2

/-- Continuous evaluation commutes with a Banach-valued circle integral.-/
theorem circleIntegral_continuousMap_apply {R : ℝ}
    {f : ℂ → C(sphere (0 : ℂ) R, ℂ)} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (ζ : sphere (0 : ℂ) R) :
    (∮ t in C(c, r), f t) ζ = ∮ t in C(c, r), f t ζ := by
  have h := (ContinuousMap.evalCLM (R := ℂ) ζ).intervalIntegral_comp_comm hf.out
  simpa only [circleIntegral, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] using h.symm

end AbelFormalization
