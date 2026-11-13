import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.PoissonMass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real boundary coordinates of the Cayley map

The unit circle minus `1` parametrizes the real line. The exact kernel
identity below preserves the Stieltjes sign convention `(x-z)⁻¹`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Metric Set
open scoped Topology
namespace Complex

/-- The real coordinate of a circle point under inverse Cayley. The
exceptional point `1` is assigned the harmless totalized value zero.-/
def cayleyBoundaryReal (ξ : Circle) : ℝ := (inverseCayleyTransform (ξ : ℂ)).re

/-- Boundary inverse Cayley coordinates have zero imaginary part.
@isnad1 id=eq.0h1v.s6.057931409526 from=translated src=- shape=0f27abc0 vocab=a86f80d8
-/
theorem im_inverseCayleyTransform_circle (ξ : Circle) :
    (inverseCayleyTransform (ξ : ℂ)).im = 0 := by
  rw [im_inverseCayleyTransform, Circle.normSq_coe]
  simp only [sub_self, zero_div]

/-- The inverse Cayley coordinate of a circle point is real.
@isnad1 id=eq.0h1v.s6.99b47d89896b from=translated src=- shape=d7ea2d6c vocab=41e3d876
-/
theorem ofReal_cayleyBoundaryReal (ξ : Circle) :
    (cayleyBoundaryReal ξ : ℂ) = inverseCayleyTransform (ξ : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [ofReal_im, im_inverseCayleyTransform_circle]

/-- Inverse Cayley is measurable on the circle, including its totalized
value at the exceptional point.
@isnad1 id=measurab.0h0v.s2.f8f7661453fb from=translated src=- shape=54c8eceb vocab=db640041
-/
theorem measurable_cayleyBoundaryReal : Measurable cayleyBoundaryReal := by
  unfold cayleyBoundaryReal inverseCayleyTransform
  fun_prop

/-- Cayley and inverse Cayley recover every finite boundary point.
@isnad1 id=eq.1h1v.s4.68ce90b9d346 from=translated src=- shape=b3c198eb vocab=7b726f2e
-/
theorem cayleyTransform_inverseCayleyTransform {w : ℂ} (hw : 1 - w ≠ 0) :
    cayleyTransform (inverseCayleyTransform w) = w := by
  have hden : inverseCayleyTransform w + I ≠ 0 := by
    intro he
    have hd : inverseCayleyTransform w = -I := eq_neg_of_add_eq_zero_left he
    rw [inverseCayleyTransform, div_eq_iff hw] at hd
    have hi : 2 * I = 0 := by
      calc
        _ = I * (1 + w) + I * (1 - w) := by ring
        _ = 0 := by rw [hd]; ring
    norm_num at hi
  unfold cayleyTransform
  apply (div_eq_iff hden).mpr
  unfold inverseCayleyTransform
  field_simp [hw]
  ring_nf

/-- The Stieltjes kernel has no pole above the real line.
@isnad1 id=ne.1h2v.s5.f006ef2868fe from=translated src=- shape=268d0601 vocab=05feb82f
-/
theorem ofReal_sub_ne_zero_of_im_pos (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (x : ℂ) - z ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [sub_im, ofReal_im, zero_im, zero_sub, neg_eq_zero] at hi
  exact (ne_of_gt hz) hi

/-- The upper-half-plane Herglotz kernel becomes the weighted Cauchy
kernel, with its affine subtraction explicitly retained.
@isnad1 id=eq.2h2v.s7.7ded46dc3680 from=translated src=- shape=a76b94eb vocab=1807cd74
-/
theorem I_mul_herglotzRieszKernel_cayleyTransform
    {z : ℂ} (hz : 0 < z.im) {ξ : Circle} (hξ : ξ ≠ 1) :
    I * herglotzRieszKernel 0 (cayleyTransform z) ξ =
      ((1 + (cayleyBoundaryReal ξ) ^ 2 : ℝ) : ℂ) *
        ((cayleyBoundaryReal ξ : ℂ) - z)⁻¹ - (cayleyBoundaryReal ξ : ℂ) := by
  have hw : 1 - (ξ : ℂ) ≠ 0 := by
    intro he
    apply hξ
    exact Circle.ext (sub_eq_zero.mp he).symm
  have hzi := add_I_ne_zero_of_im_pos hz
  have hξz : (ξ : ℂ) - cayleyTransform z ≠ 0 :=
    circle_coe_sub_ne_zero (by simpa only [mem_ball, dist_zero_right] using
      norm_cayleyTransform_lt_one hz) ξ
  have hxz := ofReal_sub_ne_zero_of_im_pos (cayleyBoundaryReal ξ) hz
  rw [eq_sub_iff_add_eq]
  apply (eq_div_iff hxz).mpr
  simp only [ofReal_add, ofReal_one, ofReal_pow, ofReal_cayleyBoundaryReal]
  rw [herglotzRieszKernel_def]
  simp only [sub_zero]
  field_simp [hξz]
  unfold inverseCayleyTransform cayleyTransform
  field_simp [hw, hzi]
  ring_nf
  simp only [I_sq, I_pow_three]
  ring
/-- The stereographic mass weight is `1+x²` in real Cayley coordinates.
@isnad1 id=eq.1h1v.s7.12f4e555d9a6 from=translated src=- shape=0e4c7e4b vocab=43c5bd73
-/
theorem one_add_sq_cayleyBoundaryReal {ξ : Circle} (hξ : ξ ≠ 1) :
    1 + (cayleyBoundaryReal ξ) ^ 2 = 2 / (1 - (ξ : ℂ).re) := by
  have hs := Circle.normSq_coe ξ
  rw [normSq_apply] at hs
  have hd : 1 - (ξ : ℂ).re ≠ 0 :=
    ne_of_gt (sub_pos.mpr (circle_re_lt_one_of_ne_one hξ))
  have hn : normSq (1 - (ξ : ℂ)) = 2 * (1 - (ξ : ℂ).re) := by
    simp only [normSq_apply, sub_re, sub_im, one_re, one_im]
    nlinarith
  have hp : normSq (1 + (ξ : ℂ)) = 2 * (1 + (ξ : ℂ).re) := by
    simp only [normSq_apply, add_re, add_im, one_re, one_im]
    nlinarith
  have he : (cayleyBoundaryReal ξ) ^ 2 =
      (1 + (ξ : ℂ).re) / (1 - (ξ : ℂ).re) := by
    calc
      _ = normSq (inverseCayleyTransform (ξ : ℂ)) := by
        rw [← ofReal_cayleyBoundaryReal, normSq_ofReal]
        ring
      _ = _ := by
        simp only [inverseCayleyTransform, normSq_div, normSq_mul, normSq_I,
          one_mul, hn, hp]
        field_simp [hd]
  rw [he]
  field_simp [hd]
  ring

end Complex
