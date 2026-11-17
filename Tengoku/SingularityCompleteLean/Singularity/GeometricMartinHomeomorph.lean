import Tengoku.SingularityCompleteLean.Singularity.CompactMartinContinuity
import Tengoku.SingularityCompleteLean.Singularity.CompactBoundaryEscape

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The full geometric Martin boundary homeomorphism

Two points admit a common finite-image chart, so finite-chart injectivity gives
injectivity on the compact boundary. Conversely, escaping finite-pole
approximations of any abstract Martin point have a geometric boundary
subsequence. The proved arbitrary-approach convergence identifies that point.
-/

noncomputable section
open Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Two prescribed boundary points can simultaneously be placed in the real
chart when the orbit of infinity is infinite.
@isnad1 id=ex.1h3v.s12.988a7b4a8244 from=translated src=- shape=15a1c5b2 vocab=3966c77f
-/
theorem exists_common_finite_image_boundary (Γ : Subgroup SL(2, ℝ))
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (p q : OnePoint ℝ) :
    ∃ (g : Γ) (ξ η : ℝ), g • p = (ξ : OnePoint ℝ) ∧ g • q = (η : OnePoint ℝ) := by
  obtain ⟨r, hr, hrnot⟩ := horbit.exists_notMem_finite (Set.toFinite ({p, q} : Set (OnePoint ℝ)))
  obtain ⟨g, rfl⟩ := hr
  have hp : g⁻¹ • p ≠ (∞ : OnePoint ℝ) := by
    intro he
    have hh := congrArg (fun z : OnePoint ℝ => g • z) he
    simp only [smul_inv_smul] at hh
    apply hrnot
    dsimp only
    rw [← hh]
    simp
  have hq : g⁻¹ • q ≠ (∞ : OnePoint ℝ) := by
    intro he
    have hh := congrArg (fun z : OnePoint ℝ => g • z) he
    simp only [smul_inv_smul] at hh
    apply hrnot
    dsimp only
    rw [← hh]
    simp
  cases he : g⁻¹ • p with
  | infty => exact (hp he).elim
  | coe ξ =>
    cases hf : g⁻¹ • q with
    | infty => exact (hq hf).elim
    | coe η => exact ⟨g⁻¹, ξ, η, he, hf⟩

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

include hmass in
/-- Distinct compact geometric boundary points have distinct Martin points.
@isnad1 id=injectiv.5h3v.s16.47f442567929 from=translated src=- shape=4fa584a2 vocab=21312463
-/
theorem compactMartinPoint_injective :
    Function.Injective (compactMartinPoint Γ s μ hpos hgen hgap horbit) := by
  intro p q he
  obtain ⟨g, ξ, η, hp, hq⟩ := exists_common_finite_image_boundary Γ horbit p q
  rw [compactMartinPoint_chart Γ s μ hpos hmass hgen hgap horbit p g ξ hp,
    compactMartinPoint_chart Γ s μ hpos hmass hgen hgap horbit q g η hq] at he
  have hh := (martinBoundaryHomeomorph s μ hpos hgen hgap 1 g⁻¹).injective he
  have hξη := rayMartinPoint_injective Γ s μ hpos hmass hgen hgap hh
  apply MulAction.injective g
  dsimp only
  rw [hp, hq, hξη]

include hmass in
/-- Every point of the actual abstract Martin boundary is geometric.
@isnad1 id=surjecti.5h3v.s16.315bab98735d from=translated src=- shape=4fa584a2 vocab=9087a123
-/
theorem compactMartinPoint_surjective :
    Function.Surjective (compactMartinPoint Γ s μ hpos hgen hgap horbit) := by
  intro H
  obtain ⟨y, hescape, hlim⟩ := martinBoundary_escaping_approximation s μ hgen 1 H
  have hf (K : Finset Γ) : ∀ᶠ n in atTop, y n ∉ K := by
    have hh := (Filter.eventually_all_finset K).mpr (fun z _ => hescape z)
    filter_upwards [hh] with n hn
    intro he
    exact hn (y n) he rfl
  obtain ⟨p, hp, φ, hφ, ht⟩ := escaping_orbit_boundary_subsequence Γ UpperHalfPlane.I y hf
  rw [← compactBoundaryEmbedding_range] at hp
  obtain ⟨q, rfl⟩ := hp
  refine ⟨q, ?_⟩
  apply Subtype.ext
  funext x
  exact tendsto_nhds_unique
    (compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit q (y ∘ φ) ht x)
    ((hlim x).comp hφ.tendsto_atTop)

include hmass in
/-- The actual compact geometric boundary map is a homeomorphism.
@isnad1 id=ishomeom.5h3v.s16.9171a454f72f from=translated src=- shape=4fa584a2 vocab=eec25cb8
-/
theorem isHomeomorph_compactMartinPoint :
    IsHomeomorph (compactMartinPoint Γ s μ hpos hgen hgap horbit) :=
  isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_compactMartinPoint Γ s μ hpos hmass hgen hgap horbit,
      compactMartinPoint_injective Γ s μ hpos hmass hgen hgap horbit,
      compactMartinPoint_surjective Γ s μ hpos hmass hgen hgap horbit⟩

/-- The constructed homeomorphism from the real projective line to the actual
Martin boundary of the finite-support walk.-/
def geometricMartinHomeomorph : OnePoint ℝ ≃ₜ martinBoundary s μ 1 :=
  (isHomeomorph_compactMartinPoint Γ s μ hpos hmass hgen hgap horbit).homeomorph _

end Singularity
