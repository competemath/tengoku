import Tengoku.PshdLean.PshLines.PSHD.FourierProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fourier transform of the difference measure

The product-measure identity used in the Fourier representation of Riesz
energy in `pshd-vibe`, Lemma 1.4.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The transform of the distribution of differences is the squared modulus
of the original transform.
@isnad1 id=eq.0h3v.s7.7ac67c89f4da from=translated src=- shape=8a3906bc vocab=bb9834a3
-/
theorem measureFourier_map_sub (μ : Measure E) [SFinite μ] (ξ : E) :
    measureFourier ((μ.prod μ).map (fun p : E × E ↦ p.1 - p.2)) ξ =
      ((‖measureFourier μ ξ‖ ^ 2 : ℝ) : ℂ) := by
  have h : charFun ((μ.prod μ).map (fun p : E × E ↦ p.1 - p.2))
      ((-2 * Real.pi) • ξ) =
      charFun μ ((-2 * Real.pi) • ξ) * charFun μ (-((-2 * Real.pi) • ξ)) := by
    simp only [charFun_apply]
    rw [integral_map (by fun_prop) (by fun_prop), ← integral_prod_mul]
    congr 1
    funext p
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, inner_neg_right]
    push_cast
    ring
  rw [charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  simpa only [measureFourier] using h

end PshLines.PSHD
