import Tengoku.SingularityCompleteLean.Singularity.CocompactExcessAncona
import Tengoku.SingularityCompleteLean.Singularity.MartinApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A reciprocal Green lower bound at a suitable Martin point

Continue a geodesic through any prescribed orbit point and approximate its tail
by orbit vertices. The triangle excess is uniformly bounded, so ordinary Ancona
passes to a Martin cluster point and gives a lower bound for G(1,x)H(x).
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Orbit approximations beyond x on a geodesic escape every fixed state and
have triangle excess bounded uniformly at x.-/
theorem cocompact_exists_beyond_sequence (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ D : ℝ, 0 < D ∧ ∀ x : Γ, ∃ y : ℕ → Γ,
      (∀ z, ∀ᶠ n in atTop, z ≠ y n) ∧ ∀ n,
      dist UpperHalfPlane.I (x • UpperHalfPlane.I) +
        dist (y n • UpperHalfPlane.I) (x • UpperHalfPlane.I) -
        dist UpperHalfPlane.I (y n • UpperHalfPlane.I) ≤ D := by
  obtain ⟨E, hE, hcover⟩ := cocompact_orbit_uniform_bound Γ
  refine ⟨2 * E, by positivity, fun x => ?_⟩
  let d := dist UpperHalfPlane.I (x • UpperHalfPlane.I)
  have hd : 0 ≤ d := dist_nonneg
  obtain ⟨c, hc, hc0, hcd⟩ := exists_hyperbolic_geodesic_line UpperHalfPlane.I (x • UpperHalfPlane.I)
  choose y hy using fun n : ℕ => hcover (c (d + n))
  have hdist0 (n : ℕ) : dist UpperHalfPlane.I (c (d + n)) = d + n := by
    rw [← hc0, hc.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ d + n)]
  have hdistx (n : ℕ) : dist (x • UpperHalfPlane.I) (c (d + n)) = n := by
    rw [← hcd, hc.dist_eq, Real.dist_eq]
    change |d - (d + n)| = n
    rw [show d - (d + n) = -(n : ℝ) by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
  have hrad (n : ℕ) : d + n - E ≤ dist UpperHalfPlane.I (y n • UpperHalfPlane.I) := by
    have h := dist_triangle UpperHalfPlane.I (y n • UpperHalfPlane.I) (c (d + n))
    rw [hdist0] at h
    linarith [hy n]
  refine ⟨y, ?_, fun n => ?_⟩
  · intro z
    have hn : ∀ᶠ n : ℕ in atTop,
        dist UpperHalfPlane.I (z • UpperHalfPlane.I) + E < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [hn] with n hn
    intro he
    have h := hrad n
    rw [← he] at h
    linarith
  · have h := dist_triangle (y n • UpperHalfPlane.I) (c (d + n)) (x • UpperHalfPlane.I)
    rw [dist_comm (c (d + n)), hdistx] at h
    change d + _ - _ ≤ _
    linarith [hy n, hrad n]

end Singularity
