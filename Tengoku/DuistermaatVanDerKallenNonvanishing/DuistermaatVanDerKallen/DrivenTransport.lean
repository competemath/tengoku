import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.DrivenContinuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Complete transport along a continuously differentiable scalar base path.
The proper-radius estimate and separation from the critical locus are proved
for every partial solution before compact-domain continuation is applied. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- The proper embedded radius obeys Gronwall with a uniform bound on the
continuous driving velocity, not the ordinary coordinate-space radius.-/
theorem laurent_driven_curve_radius_bound {d : ℕ} (f : MultiLaurent d) (v : ℝ → ℂ)
    {γ : ℝ → Fin d → ℂ} {s b c B : ℝ} (hc : 0 < c)
    (hγ : ContinuousOn γ (Icc s b))
    (hz : ∀ t ∈ Icc s b, γ t ∈ laurentRegularDomain f)
    (hd : ∀ t ∈ Ico s b, HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hv : ∀ t ∈ Ico s b, ‖v t‖ ≤ B)
    (hbound : ∀ t (ht : t ∈ Ico s b),
      c ≤ (1 + ‖torusEmbed (γ t)‖) * laurentDifferentialNorm f
        ⟨torusEmbed (γ t), embed_mem (hz t (Ico_subset_Icc_self ht)).1⟩) :
    ∀ t ∈ Icc s b, 1 + ‖torusEmbed (γ t)‖ ≤
      (1 + ‖torusEmbed (γ s)‖) * Real.exp ((B / c) * (t - s)) := by
  apply trajectory_radius_bound (x := torusEmbed ∘ γ)
    (v := fun t => torusTangentMap (γ t) (laurentVectorField f (v t) (γ t)))
  · intro t ht
    exact (torusEmbed_contDiffAt_real (hz t ht).1).continuousAt.comp_continuousWithinAt (hγ t ht)
  · intro t ht
    exact (((torusEmbed_hasFDerivAt (hz t (Ico_subset_Icc_self ht)).1).restrictScalars ℝ).comp_hasDerivAt t (hd t ht)).hasDerivWithinAt
  · intro t ht
    exact (laurentVectorField_linear_growth f (v t) (hz t (Ico_subset_Icc_self ht)) hc
      (hbound t ht)).trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hv t ht) hc.le) (by positivity))

end
end DuistermaatVanDerKallen
