import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.PositiveRepresentation
import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
import Tengoku.Seed.Analysis.Complex.OpenMapping
import Tengoku.Seed.Analysis.InnerProductSpace.Harmonic.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The scalar disk Herglotz representation

A holomorphic function with nonnegative real part is represented by an actual
positive finite unit-circle measure and its imaginary value at the center.
The positive harmonic measure is constructed by radial approximation, and
the complex integral is differentiated with a proved compact uniform bound.
Source: the scalar Herglotz theorem used by Ajanki--Erdos--Kruger (2019),
Proposition 2.1, arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set Metric Complex InnerProductSpace
open scoped Topology

namespace Complex

/-- A unit-circle point differs from every point inside the open unit disk.
@isnad1 id=ne.1h2v.s6.f211c754f61b from=translated src=- shape=73a37c94 vocab=e17e933a
-/
theorem circle_coe_sub_ne_zero {w : ℂ} (hw : w ∈ ball 0 1) (ξ : Circle) :
    (ξ : ℂ) - w ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [Circle.norm_coe] at he
  have hh : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  linarith

/-- The complex Herglotz kernel is continuous on the actual unit circle.
@isnad1 id=continuo.1h1v.s7.8652b45701a8 from=translated src=- shape=c9c3ee6e vocab=164e935b
-/
theorem continuous_herglotzRieszKernel_circle {w : ℂ} (hw : w ∈ ball 0 1) :
    Continuous (fun ξ : Circle => herglotzRieszKernel 0 w ξ) := by
  simp only [herglotzRieszKernel_def, sub_zero]
  exact (continuous_subtype_val.add continuous_const).div
    (continuous_subtype_val.sub continuous_const) (circle_coe_sub_ne_zero hw)

/-- Differentiation of the Herglotz kernel in its interior pole.
@isnad1 id=hasderiv.1h2v.s8.4dc1c2419725 from=translated src=- shape=8f62b3da vocab=f8e327d2
-/
theorem hasDerivAt_herglotzRieszKernel_pole {w : ℂ} (hw : w ∈ ball 0 1) (ξ : Circle) :
    HasDerivAt (fun z => herglotzRieszKernel 0 z ξ)
      (2 * (ξ : ℂ) / ((ξ : ℂ) - w) ^ 2) w := by
  have h := ((hasDerivAt_const w (ξ : ℂ)).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w (ξ : ℂ)).sub (hasDerivAt_id w)) (circle_coe_sub_ne_zero hw ξ)
  have h' : HasDerivAt (fun z : ℂ => ((ξ : ℂ) + z) / ((ξ : ℂ) - z))
      (((ξ : ℂ) - w + ((ξ : ℂ) + w)) / ((ξ : ℂ) - w) ^ 2) w := by
    convert! h using 1
    simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add,
      zero_sub, one_mul, mul_neg_one, sub_neg_eq_add]
  have he : (ξ : ℂ) - w + ((ξ : ℂ) + w) = 2 * (ξ : ℂ) := by ring
  simpa only [herglotzRieszKernel_def, sub_zero, he] using h'

/-- The actual Herglotz integral of any positive finite circle measure is
complex differentiable at each point of the disk. A compact neighborhood
constructs the common domination bound required under the integral.
@isnad1 id=hasderiv.1h2v.s8.b7540852d691 from=translated src=- shape=1ef2625a vocab=304a9914
-/
theorem hasDerivAt_integral_herglotzRieszKernel (μ : Measure Circle) [IsFiniteMeasure μ]
    {w : ℂ} (hw : w ∈ ball 0 1) :
    HasDerivAt (fun z => ∫ ξ : Circle, herglotzRieszKernel 0 z ξ ∂μ)
      (∫ ξ : Circle, 2 * (ξ : ℂ) / ((ξ : ℂ) - w) ^ 2 ∂μ) w := by
  let r := (1 - ‖w‖) / 2
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have hr : 0 < r := by dsimp [r]; linarith
  have hinside (z : ℂ) (hz : z ∈ closedBall w r) : z ∈ ball (0 : ℂ) 1 := by
    have hdist : ‖z - w‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hn := norm_add_le (z - w) w
    rw [sub_add_cancel] at hn
    simp only [mem_ball, dist_zero_right]
    dsimp [r] at hdist
    linarith
  let D : ℂ → Circle → ℂ := fun z ξ => 2 * (ξ : ℂ) / ((ξ : ℂ) - z) ^ 2
  have hD : ContinuousOn (fun p : ℂ × Circle => D p.1 p.2) (closedBall w r ×ˢ univ) := by
    dsimp [D]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    exact pow_ne_zero 2 (circle_coe_sub_ne_zero (hinside p.1 hp.1) p.2)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall w r).prod isCompact_univ).bddAbove_image hD.norm
  have hcontD : Continuous (D w) := by
    dsimp [D]
    exact (continuous_const.mul continuous_subtype_val).div
      ((continuous_subtype_val.sub continuous_const).pow 2)
      (fun ξ => pow_ne_zero 2 (circle_coe_sub_ne_zero hw ξ))
  have hi : Integrable (fun ξ : Circle => herglotzRieszKernel 0 w ξ) μ :=
    (continuous_herglotzRieszKernel_circle hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := closedBall w r) (bound := fun _ => B) (closedBall_mem_nhds _ hr)
    (F := fun z ξ => herglotzRieszKernel 0 z ξ) (F' := D)
    (by
      filter_upwards [closedBall_mem_nhds w hr] with z hz
      exact (continuous_herglotzRieszKernel_circle (hinside z hz)).aestronglyMeasurable)
    hi hcontD.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ z hz => hB ⟨(z, ξ), ⟨hz, mem_univ _⟩, rfl⟩))
    (integrable_const B)
    (Filter.Eventually.of_forall (fun ξ z hz => hasDerivAt_herglotzRieszKernel_pole (hinside z hz) ξ))
  exact h.2

end Complex
