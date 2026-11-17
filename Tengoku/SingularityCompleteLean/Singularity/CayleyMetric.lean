import Tengoku.SingularityCompleteLean.Singularity.CompactBoundary
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Metric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The disk coordinate and hyperbolic jump estimates

The Cayley coordinate is used quantitatively: points far from i make only
exponentially small Euclidean disk jumps when their hyperbolic distance is
bounded. This is the geometric input to the path convergence proof.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The Cayley coordinate mapping the upper half-plane into the unit disk.-/
def halfPlaneCayley (z : ℍ) : ℂ := ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)

/-- Its denominator never vanishes on the upper half-plane.
@isnad1 id=ne.0h1v.s4.a463eac42341 from=translated src=- shape=ff3278d8 vocab=a9ab1e3f
-/
theorem halfPlaneCayley_denominator_ne_zero (z : ℍ) : (z : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, UpperHalfPlane.coe_im, Complex.I_im, Complex.zero_im] at hi
  linarith [z.im_pos]

/-- Exact difference formula for disk coordinates.
@isnad1 id=eq.0h2v.s6.2fc751e82c52 from=translated src=- shape=26ffbb01 vocab=e7796f62
-/
theorem halfPlaneCayley_sub (z w : ℍ) :
    halfPlaneCayley z - halfPlaneCayley w =
      (2 * Complex.I) * ((z : ℂ) - (w : ℂ)) / (((z : ℂ) + Complex.I) * ((w : ℂ) + Complex.I)) := by
  unfold halfPlaneCayley
  field_simp [halfPlaneCayley_denominator_ne_zero z, halfPlaneCayley_denominator_ne_zero w]
  ring

/-- The Cayley denominator encodes radial hyperbolic distance.
@isnad1 id=eq.0h1v.s6.31945dfb308f from=translated src=- shape=836ce49e vocab=3584a4f1
-/
theorem halfPlaneCayley_denominator_norm (z : ℍ) :
    ‖(z : ℂ) + Complex.I‖ = 2 * Real.sqrt z.im * Real.cosh (dist z UpperHalfPlane.I / 2) := by
  have h := UpperHalfPlane.cosh_half_dist z UpperHalfPlane.I
  simp only [UpperHalfPlane.coe_I, UpperHalfPlane.I_im, mul_one, Complex.conj_I,
    dist_eq_norm, sub_neg_eq_add] at h
  have hp : 2 * Real.sqrt z.im ≠ 0 := by positivity
  have he := (div_eq_iff hp).mp h.symm
  simpa only [mul_comm] using he

/-- Exact disk distance in terms of three hyperbolic distances.
@isnad1 id=eq.0h2v.s6.81242585d5ca from=translated src=- shape=c8943872 vocab=4c63f9b4
-/
theorem halfPlaneCayley_dist (z w : ℍ) :
    dist (halfPlaneCayley z) (halfPlaneCayley w) =
      Real.sinh (dist z w / 2) /
        (Real.cosh (dist z UpperHalfPlane.I / 2) * Real.cosh (dist w UpperHalfPlane.I / 2)) := by
  have hs := UpperHalfPlane.sinh_half_dist z w
  rw [dist_eq_norm] at hs
  have hp : 2 * Real.sqrt (z.im * w.im) ≠ 0 := by positivity
  have he := (div_eq_iff hp).mp hs.symm
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [dist_eq_norm, halfPlaneCayley_sub, norm_div, norm_mul, norm_mul,
    norm_mul, Complex.norm_I, htwo, mul_one, he,
    halfPlaneCayley_denominator_norm, halfPlaneCayley_denominator_norm,
    Real.sqrt_mul z.im_pos.le]
  have hz : Real.sqrt z.im ≠ 0 := by positivity
  have hw : Real.sqrt w.im ≠ 0 := by positivity
  field_simp

/-- A simple exponential upper bound for the hyperbolic sine.
@isnad1 id=le.0h1v.s3.1110e77f97b4 from=translated src=- shape=0fc427d2 vocab=9a1773dc
-/
theorem sinh_le_exp (t : ℝ) : Real.sinh t ≤ Real.exp t := by
  rw [Real.sinh_eq]
  linarith [Real.exp_pos t, Real.exp_pos (-t)]

/-- A simple exponential lower bound for the hyperbolic cosine.
@isnad1 id=le.0h1v.s4.d476c823de10 from=translated src=- shape=ffd9fe76 vocab=72fa77cb
-/
theorem exp_le_two_cosh (t : ℝ) : Real.exp t ≤ 2 * Real.cosh t := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-t)]

/-- A jump of hyperbolic length at most L is exponentially small in the disk
coordinate as its initial point escapes from i.
@isnad1 id=le.1h3v.s6.3f37d59383dc from=translated src=- shape=520743f4 vocab=3e0047a6
-/
theorem halfPlaneCayley_dist_le (z w : ℍ) (L : ℝ) (hL : dist z w ≤ L) :
    dist (halfPlaneCayley z) (halfPlaneCayley w) ≤
      4 * Real.exp L * Real.exp (-dist z UpperHalfPlane.I) := by
  have hz := exp_le_two_cosh (dist z UpperHalfPlane.I / 2)
  have hw := exp_le_two_cosh (dist w UpperHalfPlane.I / 2)
  have hden : Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) ≤
      4 * (Real.cosh (dist z UpperHalfPlane.I / 2) * Real.cosh (dist w UpperHalfPlane.I / 2)) := by
    rw [add_div, Real.exp_add]
    nlinarith [mul_le_mul hz hw (Real.exp_pos _).le (by positivity)]
  have hnum := (sinh_le_exp (dist z w / 2)).trans (Real.exp_le_exp.mpr (by linarith : dist z w / 2 ≤ L / 2))
  have hb : Real.sinh (dist z w / 2) /
      (Real.cosh (dist z UpperHalfPlane.I / 2) * Real.cosh (dist w UpperHalfPlane.I / 2)) ≤
      4 * Real.exp (L / 2) / Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) := by
    apply (div_le_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)) (Real.exp_pos _)).mpr
    calc
      _ ≤ Real.exp (L / 2) * Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) :=
        mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
      _ ≤ Real.exp (L / 2) * (4 * (Real.cosh (dist z UpperHalfPlane.I / 2) *
          Real.cosh (dist w UpperHalfPlane.I / 2))) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = _ := by ring
  rw [halfPlaneCayley_dist]
  apply hb.trans
  rw [mul_div_assoc, ← Real.exp_sub, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have ht := dist_triangle z w UpperHalfPlane.I
  linarith

end Singularity
