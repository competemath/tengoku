import Tengoku.SingularityCompleteLean.Singularity.CocompactAxisAncona
import Tengoku.SingularityCompleteLean.Singularity.HyperbolicAxisNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-sided Ancona inequalities along constructed geodesic segments

Each endpoint pair has a unit-speed geodesic line. Uniformly in the endpoints,
a middle orbit point at distance at most K from its segment satisfies both
multiplicative Green bounds. The lower bound is the first-hit inequality; the
upper bound uses the constructed shrinking-ball iteration.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Recenter the axis bound at any parameter in the endpoint interval.-/
theorem cocompact_axis_segment_green_upper (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (K : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (g : SL(2, ℝ)) (t u : ℝ), u ∈ Set.Icc 0 t →
      ∀ x o y : Γ, g • UpperHalfPlane.I = x • UpperHalfPlane.I →
      g • verticalHeightRay UpperHalfPlane.I t = y • UpperHalfPlane.I →
      dist (g • verticalHeightRay UpperHalfPlane.I u) (o • UpperHalfPlane.I) ≤ K →
      walkGreen s μ x y ≤ H * (walkGreen s μ x o * walkGreen s μ o y) := by
  obtain ⟨H, hH, hbound⟩ := cocompact_axis_green_product_bound Γ s μ hpos hmass hgen hgap K
  refine ⟨H, hH, ?_⟩
  intro g t u hu x o y hx hy ho
  apply hbound (g * dilationMatrix u) u (t-u) hu.1 (sub_nonneg.mpr hu.2) x o y
  · rw [mul_smul, verticalHeightRay_I_dilation]
    simpa only [add_neg_cancel, verticalHeightRay_zero] using hx
  · rw [mul_smul, verticalHeightRay_I_dilation]
    simpa only [add_sub_cancel] using hy
  · have hh := verticalHeightRay_I_dilation u 0
    simp only [verticalHeightRay_zero, add_zero] at hh
    simpa only [mul_smul, hh] using ho

end Singularity
