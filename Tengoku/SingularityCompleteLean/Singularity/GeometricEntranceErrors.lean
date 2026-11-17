import Tengoku.SingularityCompleteLean.Singularity.EntrancePairTransfer
import Tengoku.SingularityCompleteLean.Singularity.CocompactRelativeDetour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform geometric errors for either entrance orientation

The actual first-entry remainder and the reflected last-entry remainder both
satisfy the previously proved relative detour estimate, with one common radius
threshold. Finite sets must be the full orbit ball, not an assumed separator.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- One geometric threshold controls the discarded mass in either orientation.
@isnad1 id=ex.3h6v.s17.262c7f68ef68 from=translated src=- shape=6028f79a vocab=e8886793
-/
theorem entrancePairRemainder_relative_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D B K : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ (u : Γ) (A : Finset Γ) (last : Bool) (p : Γ × Γ),
      (A : Set Γ) = {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} →
      2 ≤ dist (p.1 • UpperHalfPlane.I) (p.2 • UpperHalfPlane.I) →
      dist (p.1 • UpperHalfPlane.I) (p.2 • UpperHalfPlane.I) ≤ B * R →
      dist (p.1 • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (p.2 • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (p.1 • UpperHalfPlane.I) (p.2 • UpperHalfPlane.I) ≤ D →
      entrancePairRemainder s μ A last p ≤ Real.exp (-K * R) * walkGreen s μ p.1 p.2 := by
  obtain ⟨R₁, hR₁⟩ := cocompact_relative_green_detour Γ s μ hpos hgen hgap D B K
  obtain ⟨R₂, hR₂⟩ := cocompact_relative_green_detour Γ
    (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
    (reflectedMarkov_spectral_gap s μ hgap) D B K
  refine ⟨max R₁ R₂, ?_⟩
  intro R hR u A last p hA hd hdiam hexcess
  cases last
  · change killedGreen s μ (A : Set Γ) p.1 p.2 ≤ _
    rw [hA]
    exact hR₁ R ((le_max_left _ _).trans hR) u p.1 p.2 hd hdiam hexcess
  · change killedGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A : Set Γ) p.2 p.1 ≤ _
    rw [hA]
    have hh := hR₂ R ((le_max_right _ _).trans hR) u p.2 p.1
      (by simpa only [dist_comm] using hd) (by simpa only [dist_comm] using hdiam)
      (by simpa only [add_comm, dist_comm] using hexcess)
    simpa only [reflected_walkGreen s μ hgap] using hh

end Singularity
