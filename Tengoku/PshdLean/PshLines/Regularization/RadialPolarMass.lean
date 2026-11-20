import Tengoku.PshdLean.PshLines.Regularization.RadialPoissonCertificate
import Tengoku.Seed.MeasureTheory.Constructions.HaarToSphere
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Polar mass of squared-radius profiles

In positive complex dimension, Haar polar coordinates and the substitution
`s = r ^ 2` express the integral of a squared-radius profile through its
weighted one-variable integral.  Applied to the difference of two normalized
radial kernels, equality of their total masses forces that weighted integral
to vanish.

The formula is intentionally restricted to `0 < n`.  In complex dimension
zero the ambient Haar space is a singleton and the weighted `Ioi 0` expression
is not the correct polar model.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace PshLines.Regularization.RadialPolarMass

open FirstPass
open HolomorphicPullback
open RadialPoissonCertificate

/-- Polar integration for a profile of the squared norm on a positive
dimensional standard complex model.
@isnad1 id=eq.1h2v.s9.30a90df60b01 from=translated src=- shape=2e4981fc vocab=453aa025
-/
theorem integral_sqNorm_radial {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    ∫ x : ComplexModel n, f (‖x‖ ^ 2) ∂volume =
      ((n : ℝ) * volume.real (ball (0 : ComplexModel n) 1)) *
        ∫ s in Ioi (0 : ℝ), s ^ (n - 1) * f s := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let _ : Nontrivial (ComplexModel n) := inferInstance
  rw [MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (ComplexModel n)) (fun r : ℝ => f (r ^ 2))]
  rw [finrank_real_complexModel]
  have hsubst := MeasureTheory.integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => s ^ (n - 1) * f s) (p := (2 : ℝ)) (by norm_num)
  have hpoint :
      (fun r : ℝ => ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) •
          ((r ^ (2 : ℝ)) ^ (n - 1) * f (r ^ (2 : ℝ)))) =
        fun r => 2 * (r ^ (2 * n - 1) * f (r ^ 2)) := by
    funext r
    rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, pow_succ, pow_mul]
    norm_num [Real.rpow_two, Real.rpow_one]
    ring
  rw [hpoint, integral_const_mul] at hsubst
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
  rw [← hsubst]
  ring

/-- Every two normalized explicit radial kernels have zero weighted
squared-radius mass difference in positive complex dimension.
@isnad1 id=eq.2h4v.s6.8297a2a97c63 from=translated src=- shape=19db669a vocab=6dd0326a
-/
theorem integral_explicitRadialKernelSqDifference_weighted_eq_zero
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ) :
    ∫ s in Ioi (0 : ℝ), s ^ (n - 1) *
        explicitRadialKernelSqDifference (n := n) R hR a b s = 0 := by
  have hka : Integrable (explicitRadialKernel (n := n) R hR a) volume :=
    (explicitRadialKernel_contDiff R hR a).continuous.integrable_of_hasCompactSupport
      (explicitRadialKernel_hasCompactSupport R hR a)
  have hkb : Integrable (explicitRadialKernel (n := n) R hR b) volume :=
    (explicitRadialKernel_contDiff R hR b).continuous.integrable_of_hasCompactSupport
      (explicitRadialKernel_hasCompactSupport R hR b)
  have hspatial :
      ∫ x : ComplexModel n,
          (explicitRadialKernel R hR a x - explicitRadialKernel R hR b x) ∂volume = 0 := by
    rw [integral_sub hka hkb, explicitRadialKernel_integral_one,
      explicitRadialKernel_integral_one, sub_self]
  have hprofile :
      ∫ x : ComplexModel n,
          explicitRadialKernelSqDifference (n := n) R hR a b (‖x‖ ^ 2) ∂volume = 0 := by
    calc
      _ = ∫ x : ComplexModel n,
          (explicitRadialKernel R hR a x - explicitRadialKernel R hR b x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            exact (explicitRadialKernel_sub_eq_sqDifference_norm_sq R hR a b x).symm
      _ = 0 := hspatial
  have hpolar := integral_sqNorm_radial hn
    (explicitRadialKernelSqDifference (n := n) R hR a b)
  have hmul :
      ((n : ℝ) * volume.real (ball (0 : ComplexModel n) 1)) *
          ∫ s in Ioi (0 : ℝ), s ^ (n - 1) *
            explicitRadialKernelSqDifference (n := n) R hR a b s = 0 := by
    rw [← hpolar, hprofile]
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hvolume : 0 < volume.real (ball (0 : ComplexModel n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne'
      measure_ball_lt_top.ne
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hnReal.ne' hvolume.ne')

end PshLines.Regularization.RadialPolarMass
