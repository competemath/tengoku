/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.HarmonicGaussian
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def radialExp (q : ℂ) (w : V) : ℂ :=
  Complex.exp (q * (‖w‖ ^ 2 : ℝ))

/--
@isnad1 id=hasfderi.0h3v.s11.74e53ecd8c51 from=translated src=- shape=2e4b569e vocab=6a377188
-/
theorem hasFDerivAt_radialExp (q : ℂ) (w : V) :
    HasFDerivAt (radialExp q)
      (Complex.exp (q * (‖w‖ ^ 2 : ℝ)) •
        (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ w)))) w := by
  unfold radialExp
  apply HasFDerivAt.cexp
  apply HasFDerivAt.const_mul
  exact Complex.ofRealCLM.hasFDerivAt.comp w
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt

/--
@isnad1 id=eq.0h4v.s8.f54fc009dfa0 from=translated src=- shape=30d26aa6 vocab=250cbc9a
-/
theorem fderiv_radialExp_apply (q : ℂ) (w x : V) :
    fderiv ℝ (radialExp q) w x =
      Complex.exp (q * (‖w‖ ^ 2 : ℝ)) * q * (2 * inner ℝ w x) := by
  rw [(hasFDerivAt_radialExp q w).fderiv]
  simp [mul_assoc]

def radialExpFirst (q : ℂ) (y z : V) : ℂ :=
  radialExp q z * q * ((2 * inner ℝ z y : ℝ) : ℂ)

/--
@isnad1 id=hasfderi.0h4v.s12.aecadf1506fe from=translated src=- shape=cfc1e081 vocab=b756741a
-/
theorem hasFDerivAt_radialExpFirst (q : ℂ) (y w : V) :
    HasFDerivAt (radialExpFirst q y)
      (radialExp q w •
          (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ y))) +
        (q * ((2 * inner ℝ w y : ℝ) : ℂ)) •
          (Complex.exp (q * (‖w‖ ^ 2 : ℝ)) •
            (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ w))))) w := by
  unfold radialExpFirst
  have hlin : HasFDerivAt (fun z : V => q * (2 * inner ℝ z y : ℝ))
      (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ y))) w := by
    convert (q • (Complex.ofRealCLM.comp (2 • innerSL ℝ y))).hasFDerivAt using 1
    ext z
    simp [real_inner_comm]
  apply ((hasFDerivAt_radialExp q w).mul hlin).congr_of_eventuallyEq
  filter_upwards with z
  simp only [Pi.mul_apply]
  ring

/--
@isnad1 id=eq.0h5v.s9.5174b4a2924b from=translated src=- shape=59a8e43d vocab=45e302ac
-/
theorem fderiv_radialExpFirst_apply (q : ℂ) (y w x : V) :
    fderiv ℝ (radialExpFirst q y) w x =
      Complex.exp (q * (‖w‖ ^ 2 : ℝ)) *
        (4 * q ^ 2 * inner ℝ w x * inner ℝ w y +
          2 * q * inner ℝ x y) := by
  rw [(hasFDerivAt_radialExpFirst q y w).fderiv]
  simp [radialExp, real_inner_comm]
  ring

/--
@isnad1 id=eq.0h5v.s8.fde70669dfb4 from=translated src=- shape=30565e83 vocab=728f9d3c
-/
theorem iteratedFDeriv_two_radialExp_apply (q : ℂ) (w x y : V) :
    iteratedFDeriv ℝ 2 (radialExp q) w ![x, y] =
      Complex.exp (q * (‖w‖ ^ 2 : ℝ)) *
        (4 * q ^ 2 * inner ℝ w x * inner ℝ w y +
          2 * q * inner ℝ x y) := by
  rw [iteratedFDeriv_two_apply]
  have hsmooth : ContDiff ℝ ⊤ (radialExp q : V → ℂ) := by
    unfold radialExp
    have hnorm : ContDiff ℝ ⊤ (fun w : V => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
    exact Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hnorm))
  have hc : DifferentiableAt ℝ (fderiv ℝ (radialExp q : V → ℂ)) w :=
    ((hsmooth.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)) w
  have happ :
      fderiv ℝ (fun z : V => fderiv ℝ (radialExp q) z y) w x =
        fderiv ℝ (fderiv ℝ (radialExp q)) w x y := by
    rw [fderiv_clm_apply hc (differentiableAt_const (c := y))]
    simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at *
  rw [← happ]
  have heq : (fun z : V => fderiv ℝ (radialExp q) z y) = radialExpFirst q y := by
    funext z
    simpa [radialExpFirst, radialExp] using fderiv_radialExp_apply q z y
  rw [heq, fderiv_radialExpFirst_apply]

end SRG266.Lattice
