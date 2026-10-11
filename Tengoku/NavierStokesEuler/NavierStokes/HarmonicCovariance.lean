import Tengoku.NavierStokesEuler.NavierStokes.CorrectionState
import Tengoku.NavierStokesEuler.NavierStokes.WaveInteractionBounds
import Tengoku.NavierStokesEuler.NavierStokes.HarmonicResidual

/-!
# Covariance of actual finite real harmonic fields

Angular integration is evaluated exactly before applying the weighted product
estimates. Real projection includes both conjugate harmonics. The constants are
uniform over a fixed bound on the harmonic index.
-/

noncomputable section

namespace NavierStokes.HarmonicCovariance

open Set Filter MeasureTheory CorrectionState
open scoped BigOperators ContDiff Topology

section CoefficientCovariance

open HarmonicFields WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The zero harmonic of a genuine finite harmonic product has the sum
of its input orders. A common finite set, rather than a support cardinality
bound, makes the estimate uniform in the band. -/
theorem angularProduct_mem {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (a b : ℕ → Coefficients D) (F : Finset ℤ)
    (hF : ∀ n, (a n).support ⊆ F)
    (ha : ∀ j ∈ F, WaveClass s P α (fun n x => a n j x))
    (hb : ∀ j ∈ F, WaveClass s P β (fun n x => b n (-j) x))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (k : ℕ → ℝ) (phase : ℕ → D → ℝ) (kp : ℕ → ℤ) (hkp : ∀ n, kp n ≠ 0) :
    MeanClass s (α + β) (fun n x => HarmonicFields.angularMean
      (fun θ => field (a n) (k n) (phase n) (kp n) (x, θ) *
        field (b n) (k n) (phase n) (kp n) (x, θ))) := by
  have hsum : MeanClass s (α + β)
      (fun n x => ∑ j ∈ F, a n j x * b n (-j) x) :=
    MemClass.sum F _ (fun _ x hx => s.zeta_nonneg x hx)
      (fun j hj => WaveInteractionBounds.wave_cmul_mean (ha j hj) (hb j hj) hP0 hP1)
  apply WaveInteractionBounds.class_congr hsum
  intro n x _
  dsimp only
  rw [angularMean_product (a n) (b n) (k n) (phase n) (hkp n) x]
  symm
  apply Finset.sum_subset (hF n)
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj]
  simp

end CoefficientCovariance

section RealCoefficientCovariance

open HarmonicFields WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem realCoefficients_mem {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (a : ℕ → Coefficients D)
    (ha : ∀ j, WaveClass s P α (fun n x => a n j x)) (j : ℤ) :
    WaveClass s P α (fun n x => HarmonicResidual.realCoefficients (a n) j x) := by
  simp only [HarmonicResidual.realCoefficients_apply]
  exact WaveInteractionBounds.class_const_cmul ((ha j).add (WaveInteractionBounds.class_conj (ha (-j))))
    (2 : ℂ)⁻¹

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realAngularProduct_eq (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : D) :
    HarmonicResidual.realAngularMean (fun θ =>
      (field a k Φ kp (x, θ)).re * (field b k Φ kp (x, θ)).re) =
      (HarmonicFields.angularMean (fun θ =>
        field (HarmonicResidual.realCoefficients a) k Φ kp (x, θ) *
        field (HarmonicResidual.realCoefficients b) k Φ kp (x, θ))).re := by
  have hc := HarmonicFields.angularMean_field
    (HarmonicResidual.realCoefficients a * HarmonicResidual.realCoefficients b) k Φ hkp x
  simp only [HarmonicFields.field_mul] at hc
  rw [hc]
  simpa only [HarmonicFields.field_mul, HarmonicResidual.field_realCoefficients,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    HarmonicResidual.realAngularMean_field
      (HarmonicResidual.realCoefficients a * HarmonicResidual.realCoefficients b) k Φ hkp x

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularAverage_add {f g : OscillatoryScalar D}
    (hf : ∀ n x, Continuous (fun θ : ℝ => f n (x, θ)))
    (hg : ∀ n x, Continuous (fun θ : ℝ => g n (x, θ))) :
    angularAverage (f + g) = angularAverage f + angularAverage g := by
  funext n x
  exact HarmonicResidual.realAngularMean_add (hf n x) (hg n x)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularProduct_add_error (A B C E : OscillatoryScalar D)
    (hA : ∀ n x, Continuous (fun θ : ℝ => A n (x, θ)))
    (hB : ∀ n x, Continuous (fun θ : ℝ => B n (x, θ)))
    (hC : ∀ n x, Continuous (fun θ : ℝ => C n (x, θ)))
    (hE : ∀ n x, Continuous (fun θ : ℝ => E n (x, θ))) :
    angularAverage ((A + C) * (B + E)) - angularAverage (A * B) =
      angularAverage (A * E) + angularAverage (C * B) + angularAverage (C * E) := by
  have he : (A + C) * (B + E) = A * B + (A * E + C * B + C * E) := by
    funext n p
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [he, angularAverage_add
    (fun n x => (hA n x).mul (hB n x))
    (fun n x => ((hA n x).mul (hE n x)).add ((hC n x).mul (hB n x)) |>.add
      ((hC n x).mul (hE n x))),
    angularAverage_add
      (fun n x => ((hA n x).mul (hE n x)).add ((hC n x).mul (hB n x)))
      (fun n x => (hC n x).mul (hE n x)),
    angularAverage_add
      (fun n x => (hA n x).mul (hE n x))
      (fun n x => (hC n x).mul (hB n x))]
  abel

end RealCoefficientCovariance

end NavierStokes.HarmonicCovariance
