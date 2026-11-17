import Tengoku.SingularityCompleteLean.Singularity.CocompactExcessAncona
import Tengoku.SingularityCompleteLean.Singularity.CocompactRayApproximation
import Tengoku.SingularityCompleteLean.Singularity.MartinCompactness
import Tengoku.SingularityCompleteLean.Singularity.GreenVanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative bounds for Martin limits along rays

Ancona comparison along uniformly approximated rays bounds the Martin value
at an earlier ray point by constant multiples of the reciprocal Green function.
These inequalities pass to every subsequential limit. Green-row vanishing
then forces such a limit to grow to infinity along its own ray.
-/

noncomputable section
open Filter
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/--
@isnad1 id=eq.0h3v.s4.6c9d6311bd81 from=translated src=- shape=106da2c7 vocab=ce5f8970
-/
theorem finiteBoundaryRay_dist_eq (ξ a b : ℝ) :
    dist (finiteBoundaryRay ξ a) (finiteBoundaryRay ξ b) = |a-b| := by
  unfold finiteBoundaryRay
  rw [dist_smul, verticalHeightRay_dist_eq]

/-- Earlier and later points of the chosen orbit ray have uniformly bounded
triangle excess at the earlier point.
@isnad1 id=le.1h4v.s13.d821d9001fe9 from=translated src=- shape=9c371ee5 vocab=c782910f
-/
theorem cocompactRaySequence_triangle_excess (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] (ξ : ℝ) (m n : ℕ) (hmn : m ≤ n) :
    dist UpperHalfPlane.I (cocompactRaySequence Γ ξ m • UpperHalfPlane.I) +
      dist (cocompactRaySequence Γ ξ n • UpperHalfPlane.I) (cocompactRaySequence Γ ξ m • UpperHalfPlane.I) -
      dist UpperHalfPlane.I (cocompactRaySequence Γ ξ n • UpperHalfPlane.I) ≤ 4 * cocompactOrbitRadius Γ := by
  have hm := cocompactRaySequence_bound Γ ξ m
  have hn := cocompactRaySequence_bound Γ ξ n
  have hd₁ := finiteBoundaryRay_dist ξ (Nat.cast_nonneg m)
  have hd₂ := finiteBoundaryRay_dist ξ (Nat.cast_nonneg n)
  have hdmn : dist (finiteBoundaryRay ξ (n:ℝ)) (finiteBoundaryRay ξ (m:ℝ)) = (n:ℝ)-m := by
    rw [finiteBoundaryRay_dist_eq, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hmn))]
  have h₁ := dist_triangle UpperHalfPlane.I (finiteBoundaryRay ξ (m:ℝ))
    (cocompactRaySequence Γ ξ m • UpperHalfPlane.I)
  have h₂ := dist_triangle UpperHalfPlane.I (cocompactRaySequence Γ ξ n • UpperHalfPlane.I)
    (finiteBoundaryRay ξ (n:ℝ))
  have h₃ := dist_triangle4 (cocompactRaySequence Γ ξ n • UpperHalfPlane.I)
    (finiteBoundaryRay ξ (n:ℝ)) (finiteBoundaryRay ξ (m:ℝ))
    (cocompactRaySequence Γ ξ m • UpperHalfPlane.I)
  rw [hd₁, dist_comm (finiteBoundaryRay ξ (m:ℝ))] at h₁
  rw [hd₂] at h₂
  rw [hdmn, dist_comm (finiteBoundaryRay ξ (m:ℝ))] at h₃
  linarith

/-- Finite Martin quotients at earlier points of an orbit ray have uniform
reciprocal-Green bounds, independent of the ray direction and both times.
@isnad1 id=ex.4h3v.s16.ce9677e44ef3 from=translated src=- shape=b40c299b vocab=59e605ed
-/
theorem cocompact_ray_martin_bounds (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : ℝ) (m n : ℕ), m ≤ n →
      walkGreen s μ 1 (cocompactRaySequence Γ ξ m) *
        martinQuotient s μ 1 (cocompactRaySequence Γ ξ m) (cocompactRaySequence Γ ξ n) ∈
          Set.Icc (1/C) (walkGreen s μ 1 1) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  obtain ⟨C, hC, hb⟩ := cocompact_excess_green_product_bound Γ s μ hpos hmass hgen hgap
    (4 * cocompactOrbitRadius Γ)
  refine ⟨C, hC, ?_⟩
  intro ξ m n hmn
  let x := cocompactRaySequence Γ ξ m
  let y := cocompactRaySequence Γ ξ n
  have hupper := hb 1 x y (by simpa only [one_smul] using cocompactRaySequence_triangle_excess Γ ξ m n hmn)
  have hlower := walkGreen_product_le s μ (fun g hg => (hpos g hg).le) hmass hgap 1 x y
  have hdiag : walkGreen s μ x x = walkGreen s μ 1 1 := by
    simpa only [mul_one] using walkGreen_left s μ x 1 1
  rw [hdiag] at hlower
  have hy := walkGreen_pos s μ hpos hgen hgap (1:Γ) y
  change 1/C ≤ walkGreen s μ 1 x * (walkGreen s μ x y / walkGreen s μ 1 y) ∧
    walkGreen s μ 1 x * (walkGreen s μ x y / walkGreen s μ 1 y) ≤ walkGreen s μ 1 1
  rw [← mul_div_assoc]
  constructor
  · apply (div_le_div_iff₀ hC hy).mpr
    nlinarith
  · exact (div_le_iff₀ hy).mpr hlower

/-- The same ray bounds hold for every subsequential Martin limit.
@isnad1 id=ex.4h3v.s16.43f1b090fbf3 from=translated src=- shape=d44a371b vocab=3ac503aa
-/
theorem cocompact_ray_martin_limit_bounds (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : ℝ) (H : Γ → ℝ) (φ : ℕ → ℕ), StrictMono φ →
      (∀ z, Tendsto (fun n => martinQuotient s μ 1 z (cocompactRaySequence Γ ξ (φ n))) atTop (𝓝 (H z))) →
      ∀ m, walkGreen s μ 1 (cocompactRaySequence Γ ξ m) * H (cocompactRaySequence Γ ξ m) ∈
        Set.Icc (1/C) (walkGreen s μ 1 1) := by
  obtain ⟨C, hC, hb⟩ := cocompact_ray_martin_bounds Γ s μ hpos hmass hgen hgap
  refine ⟨C, hC, ?_⟩
  intro ξ H φ hφ hH m
  have ht := (hH (cocompactRaySequence Γ ξ m)).const_mul (walkGreen s μ 1 (cocompactRaySequence Γ ξ m))
  have he := (hφ.tendsto_atTop.eventually (eventually_ge_atTop m)).mono (fun n hn => hb ξ m (φ n) hn)
  exact ⟨ge_of_tendsto ht (he.mono (fun _ h => h.1)), le_of_tendsto ht (he.mono (fun _ h => h.2))⟩

end Singularity
