import Tengoku.Seed.Analysis.Complex.HasPrimitives
import Tengoku.Seed.Analysis.Calculus.MeanValue
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A normalized holomorphic logarithm on a ball

A nowhere-zero holomorphic function on an open complex ball has a
holomorphic logarithm after normalization by its center value. The proof
constructs a primitive of `g' / g` and shows `g * exp(-h)` is constant.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

/-- A normalized holomorphic logarithm and its logarithmic derivative.
All function identities hold on the stated open ball.-/
theorem exists_normalized_holomorphic_log_on_ball (g : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hgn : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧ h c = 0 ∧
      (∀ z ∈ ball c R, Complex.exp (h z) = g z / g c) ∧
      (∀ z ∈ ball c R, deriv h z = deriv g z / g z) := by
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (hg.deriv isOpen_ball).div hg hgn
  obtain ⟨h, hc, hh⟩ := hd.isExactOn_ball.with_val_at c (0 : ℂ)
  have hcenter : c ∈ ball c R := mem_ball_self hR
  have hk (z : ℂ) (hz : z ∈ ball c R) :
      HasDerivAt (fun w => g w * Complex.exp (-h w)) 0 z := by
    have hcalc : HasDerivAt (fun w => g w * Complex.exp (-h w))
        (deriv g z * Complex.exp (-h z) +
          g z * (Complex.exp (-h z) * -(deriv g z / g z))) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul (hh z hz).neg.cexp
    have hzero : deriv g z * Complex.exp (-h z) +
        g z * (Complex.exp (-h z) * -(deriv g z / g z)) = 0 := by
      field_simp [hgn z hz]
      ring
    simpa only [hzero] using hcalc
  have hconst (z : ℂ) (hz : z ∈ ball c R) :
      g z * Complex.exp (-h z) = g c := by
    have heq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (show DifferentiableOn ℂ (fun w => g w * Complex.exp (-h w)) (ball c R) from
        fun w hw => (hk w hw).differentiableAt.differentiableWithinAt)
      (show Set.EqOn (deriv (fun w => g w * Complex.exp (-h w))) 0 (ball c R) from
        fun w hw => (hk w hw).deriv) hz hcenter
    simpa only [hc, neg_zero, Complex.exp_zero, mul_one] using heq
  refine ⟨h, (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt), hc,
    ?_, (fun z hz => (hh z hz).deriv)⟩
  intro z hz
  apply (eq_div_iff (hgn c hcenter)).mpr
  calc
    Complex.exp (h z) * g c =
        Complex.exp (h z) * (g z * Complex.exp (-h z)) := by rw [hconst z hz]
    _ = g z * (Complex.exp (h z) * Complex.exp (-h z)) := by ring
    _ = g z := by rw [← Complex.exp_add]; simp

end TwinPrime.Analytic
