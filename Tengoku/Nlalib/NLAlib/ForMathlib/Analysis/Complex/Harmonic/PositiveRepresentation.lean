import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.CircleProbability
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.CompactLaplaceLimit
import Tengoku.Seed.Analysis.Complex.Harmonic.Poisson
import Tengoku.Seed.MeasureTheory.Measure.WithDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive harmonic functions represented by finite circle measures

The positive measures are constructed from the radial boundary densities.
The native Poisson formula and compactness of finite measures give one
representing measure for all points in the disk. No boundary limits or
representing-measure assumption is required.
Source: the scalar Herglotz representation used in Ajanki--Erdos--Kruger
(2019), Proposition 2.1, arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set Metric Complex Real InnerProductSpace
open scoped Topology NNReal

namespace Complex

/-- The native Poisson kernel is a continuous test on the unit circle
when its pole lies strictly inside the disk.-/
theorem continuous_poissonKernel_circle {w : ℂ} (hw : w ∈ ball 0 1) :
    Continuous (fun ξ : Circle => poissonKernel 0 w ξ) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  have hcoe : Continuous (fun ξ : Circle => (ξ : ℂ)) := continuous_subtype_val
  have hc : Continuous (fun ξ : Circle => herglotzRieszKernel 0 w ξ) :=
    (continuousOn_herglotzRieszKernel_sphere hw).comp_continuous
      hcoe (by
        intro ξ
        simpa only [mem_sphere, dist_zero_right, abs_one] using Circle.norm_coe ξ)
  exact Complex.continuous_re.comp hc

/-- Scaling both the boundary point and the pole by a nonzero real
number leaves the Poisson kernel unchanged.-/
theorem poissonKernel_zero_mul_real (r : ℝ) (hr : r ≠ 0) (w ξ : ℂ) :
    poissonKernel 0 ((r : ℂ) * w) ((r : ℂ) * ξ) = poissonKernel 0 w ξ := by
  simp only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def, sub_zero]
  congr 1
  rw [← mul_add, ← mul_sub, mul_div_mul_left _ _ (by exact_mod_cast hr)]

end Complex

namespace InnerProductSpace

end InnerProductSpace
