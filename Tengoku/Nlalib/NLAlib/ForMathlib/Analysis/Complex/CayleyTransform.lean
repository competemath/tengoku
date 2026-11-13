import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cayley coordinates for the upper half plane

The rational maps identify the complex unit disk and the open upper half
plane. Their exact kernel identity transports the finite-circle Herglotz
representation to real-line Stieltjes kernels.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1, scalar Herglotz bridge.
-/

noncomputable section
open Metric Set
namespace Complex

/-- The Cayley map from the upper half plane to the unit disk.-/
def cayleyTransform (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley map from the unit disk to the upper half plane.-/
def inverseCayleyTransform (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The upper-half-plane Cayley denominator does not vanish.
@isnad1 id=ne.1h1v.s4.d24445d4e4e1 from=translated src=- shape=0ee30518 vocab=85a8296c
-/
theorem add_I_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at hi
  linarith

/-- The inverse Cayley denominator does not vanish inside the disk.
@isnad1 id=ne.1h1v.s5.66695d3f34f3 from=translated src=- shape=e0aee735 vocab=0fcc4b44
-/
theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp only [he, norm_one, lt_self_iff_false] at hw

/-- The Cayley map sends each point of the upper half plane into the disk.
@isnad1 id=lt.1h1v.s4.456ea21fe053 from=translated src=- shape=57faaa14 vocab=0729b0a0
-/
theorem norm_cayleyTransform_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖cayleyTransform z‖ < 1 := by
  have hd : 0 < normSq (z + I) := normSq_pos.mpr (add_I_ne_zero_of_im_pos hz)
  have hs : normSq (cayleyTransform z) < 1 := by
    rw [cayleyTransform, normSq_div, div_lt_one hd]
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, I_re, I_im]
    nlinarith
  rw [normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cayleyTransform z)]

/-- The imaginary part of the inverse Cayley map is the disk defect
divided by the squared denominator.
@isnad1 id=eq.0h1v.s6.ce80b3e26259 from=translated src=- shape=971c8f56 vocab=3271fa52
-/
theorem im_inverseCayleyTransform (w : ℂ) :
    (inverseCayleyTransform w).im = (1 - normSq w) / normSq (1 - w) := by
  simp only [inverseCayleyTransform, div_im, mul_re, mul_im, add_re, add_im,
    sub_re, sub_im, one_re, one_im, I_re, I_im, normSq_apply]
  ring

/-- The inverse Cayley map has positive imaginary part in the unit disk.
@isnad1 id=lt.1h1v.s4.ae2db45b14e3 from=translated src=- shape=524797ef vocab=1fe64e52
-/
theorem im_inverseCayleyTransform_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (inverseCayleyTransform w).im := by
  rw [im_inverseCayleyTransform]
  have hn : normSq w < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  exact div_pos (by linarith) (normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hw))

/-- The inverse Cayley map is analytic throughout the open unit disk.
@isnad1 id=analytic.0h0v.s5.22df53a4097f from=translated src=- shape=893cdd06 vocab=19e524f3
-/
theorem analyticOnNhd_inverseCayleyTransform :
    AnalyticOnNhd ℂ inverseCayleyTransform (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_norm_lt_one hw')

/-- The Cayley map is analytic throughout the open upper half plane.
@isnad1 id=analytic.0h0v.s5.31e4a2d39d2e from=translated src=- shape=71829fdc vocab=6e3fb86e
-/
theorem analyticOnNhd_cayleyTransform :
    AnalyticOnNhd ℂ cayleyTransform {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const)
    (add_I_ne_zero_of_im_pos hz)

/-- The finite Cayley image never equals the missing boundary point `1`.
@isnad1 id=ne.1h1v.s5.54805b4a3e0b from=translated src=- shape=45af84cc vocab=7f735501
-/
theorem one_sub_cayleyTransform_ne_zero {z : ℂ} (hz : z + I ≠ 0) :
    1 - cayleyTransform z ≠ 0 := by
  intro h
  have he : z - I = z + I :=
    (div_eq_one_iff_eq hz).mp (sub_eq_zero.mp h).symm
  have hi := congrArg Complex.im he
  simp only [sub_im, add_im, I_im] at hi
  linarith

/-- The inverse Cayley map recovers each finite upper-half-plane point.
@isnad1 id=eq.1h1v.s4.fb6473104ad4 from=translated src=- shape=a8e812f8 vocab=4136659d
-/
theorem inverseCayleyTransform_cayleyTransform {z : ℂ} (hz : z + I ≠ 0) :
    inverseCayleyTransform (cayleyTransform z) = z := by
  apply (div_eq_iff (one_sub_cayleyTransform_ne_zero hz)).mpr
  unfold cayleyTransform
  field_simp [hz]
  ring_nf

/-- The center of the disk corresponds to the upper-half-plane point `i`.
@isnad1 id=eq.0h0v.s3.2bb00c9f5266 from=translated src=- shape=0ae4dc79 vocab=47f54bfa
-/
@[simp] theorem inverseCayleyTransform_zero : inverseCayleyTransform 0 = I := by
  simp only [inverseCayleyTransform, add_zero, sub_zero, mul_one, div_one]

end Complex
