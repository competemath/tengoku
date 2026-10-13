/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all Tengoku.LeanPool.LeanPool.SpherePacking.GammaAnalysis
public import Tengoku
import Tengoku

/-!
# SaddleAnalysis

Saddle contours, Gaussian profiles, and source estimates.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped ContDiff Topology

/-! ### Sign-indexed saddle data

The plus and minus saddle constructions differ only in their polynomial factor
(`plusPolynomial` versus `minusPolynomial`).  `SaddleSign` selects one of the two, and the
dictionary below transports the facts both constructions share, so that the remaining
analysis is carried out once for both signs. -/

private inductive SaddleSign
  | plus
  | minus

private noncomputable def SaddleSign.polynomial : SaddleSign → ℝ → ℂ → ℂ
  | .plus => plusPolynomial
  | .minus => minusPolynomial

private noncomputable def SaddleSign.mellinData : SaddleSign → ℝ → ℝ → ℂ → ℂ
  | .plus => plusSaddleMellinData
  | .minus => minusSaddleMellinData

private noncomputable def SaddleSign.profile : SaddleSign → ℝ → ℝ → ℝ → ℂ
  | .plus => plusSaddleProfile
  | .minus => minusSaddleProfile

private noncomputable def SaddleSign.saddleFunction :
    SaddleSign → ℝ → (d : ℕ) → Euclidean d → ℂ
  | .plus => plusSaddleFunction
  | .minus => minusSaddleFunction

private noncomputable def SaddleSign.poleResidue : SaddleSign → ℝ → ℝ → ℕ → ℂ
  | .plus => plusSaddlePoleResidue
  | .minus => minusSaddlePoleResidue

private noncomputable def SaddleSign.taylorRemainder : SaddleSign → ℝ → ℝ → ℕ → ℝ → ℂ
  | .plus => plusSaddleTaylorRemainder
  | .minus => minusSaddleTaylorRemainder

end

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def saddleSourceMellinContour (ℓ u T : ℝ) : ℂ :=
  ((ℓ * (1 + u) : ℝ) : ℂ) -
    Complex.I * ((ℓ * T : ℝ) : ℂ)

private noncomputable def saddleSourceShellDerivative (ε u : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * a * Real.sinh (u * a)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a * Real.sinh (u * a))

private noncomputable def saddleSmallRadiusStarOrdinate (d : ℕ) : ℝ :=
  show ℝ from
    -1 + Real.log ((d : ℝ) / 2) /
      (4 * ((d : ℝ) / 2))

private noncomputable def saddleSmallRadiusStar (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp
    (saddleLogRadius ε d
      (saddleSmallRadiusStarOrdinate d))

private noncomputable def saddleSmallResidueTruncation (ℓ : ℝ) : ℕ :=
  Nat.ceil (20 * Real.log ℓ)

private noncomputable def saddleSmallResidueTailMajorant (C ℓ : ℝ) : ℝ :=
  Real.exp (3 * C - (77 / 8 : ℝ) * Real.log ℓ)

private noncomputable def saddleSmallResidueCoefficientMajorant
    (K C ℓ : ℝ) : ℝ :=
  K *
    Real.exp
      (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
    (2 * (Real.log ℓ / 8 + C) +
      (Real.log ℓ / 8 + C) ^ 2) *
    Real.exp
      (2 * C - (3 / 4 : ℝ) * Real.log ℓ)

private noncomputable def saddleSmallResidueRelativeErrorMajorant
    (K C ℓ : ℝ) : ℝ :=
  saddleSmallResidueCoefficientMajorant K C ℓ +
    2 * saddleSmallResidueTailMajorant C ℓ

end

section

open Filter Set MeasureTheory
open scoped Topology BigOperators

private noncomputable def saddleNegativeRelativeGammaTailMajorant
    (C K Kε ℓ : ℝ) : ℝ :=
  (2 * Kε / Real.Gamma (3 / 2 : ℝ)) *
    (1 + (Real.log ℓ / 8 + C)) *
      saddleSmallResidueTailMajorant C ℓ *
        Real.exp
          (K *
            (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
              ℓ)

end

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private noncomputable def upperCosLaplaceKernel (c T a : ℝ) : ℝ :=
  (1 - Real.cos (a * T)) * Real.exp (-c * a) / a

private noncomputable def upperGammaTruncatedDampingIntegrand
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  upperCosLaplaceKernel η T a *
    ∑ k ∈ Finset.range (n + 1),
      Real.exp (-(2 * a / ℓ)) ^ k

end

section

open Filter MeasureTheory Set
open scoped Topology

end

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private noncomputable def saddleNegativeContourOrdinate (ℓ : ℝ) (N : ℕ) : ℝ :=
  1 + (2 * (N : ℝ) + 1) / ℓ

private noncomputable def saddleNegativeGammaRate (ℓ : ℝ) (N : ℕ) : ℝ :=
  (2 * (N : ℝ) + 3) / ℓ

private noncomputable def saddleNegativeFrequencyMajorant (ε s : ℝ) : ℝ :=
  (1 + |s|) ^ 3 * Real.exp (-ε * Real.pi * |s|)

private noncomputable def saddleNegativeMellinMajorantCoefficient
    (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  27 * (1 + |(ε / 4)|) *
    Real.exp (2 * ε * Real.log 2) *
    (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
    Real.exp
      ((ℓ - saddleTaylorContour N) *
        Real.log Real.pi / 2) *
    Real.exp
      (ℓ * realHyperbolicShellPhase ε
        (saddleNegativeContourOrdinate ℓ N))

private noncomputable def saddleNegativeFrequencyMass (ε : ℝ) : ℝ :=
  ∫ s : ℝ, saddleNegativeFrequencyMajorant ε s

private noncomputable def saddleNegativeContourPhaseError
    (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  ℓ *
      (realHyperbolicShellPhase ε
        (saddleNegativeContourOrdinate ℓ N) -
          realHyperbolicShellPhase ε 1) -
    (((2 * N + 1 : ℕ) : ℝ) *
      saddleShellDerivativeOne ε)

private noncomputable def saddleNegativeRelativeCoefficient (ε : ℝ) : ℝ :=
  27 * (1 + |(ε / 4)|) *
    Real.exp (2 * ε * Real.log 2) *
      saddleNegativeFrequencyMass ε / (4 * (ε / 4))

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

private noncomputable def saddlePositiveCpow (z : ℂ) (x : ℝ) : ℂ :=
  ((max x 0 : ℝ) : ℂ) ^ z

private noncomputable def saddleContourExponent (a t : ℝ) : ℂ :=
  -(((a : ℂ) + (t : ℂ) * Complex.I) / 2)

@[simp] private theorem saddleContourExponent_re (a t : ℝ) :
    (saddleContourExponent a t).re = -a / 2 := by
  simp only [saddleContourExponent, Complex.neg_re, Complex.div_ofNat_re, Complex.add_re,
    Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  ring

private noncomputable def saddleContourExponentPolynomial (a : ℝ) : Polynomial ℂ :=
  Polynomial.C (-(a : ℂ) / 2) -
    Polynomial.C (Complex.I / 2) * Polynomial.X

private noncomputable def saddleContourFallingPolynomial (a : ℝ) (j : ℕ) :
    Polynomial ℂ :=
  ∏ i ∈ Finset.range j,
    (saddleContourExponentPolynomial a -
      Polynomial.C (i : ℂ))

private noncomputable def saddlePositiveContourMoment
    (a : ℝ) (j : ℕ) (D : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ,
    saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u *
      ((saddleContourFallingPolynomial a j).eval
        (t : ℂ) * D t)

private theorem saddleContourExponent_sub_nat_re
    (a t : ℝ) (j : ℕ) :
    (saddleContourExponent a t - (j : ℂ)).re =
      -a / 2 - (j : ℝ) := by
  simp only [Complex.sub_re, saddleContourExponent_re, Complex.natCast_re]

@[simp] private theorem saddlePositiveContourMoment_zero
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) < -a / 2) (D : ℝ → ℂ) :
    saddlePositiveContourMoment a j D 0 = 0 := by
  unfold saddlePositiveContourMoment
  have hzero :
      (fun t : ℝ =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) 0 *
          ((saddleContourFallingPolynomial a j).eval
              (t : ℂ) * D t)) =
        fun _ : ℝ => (0 : ℂ) := by
    funext t
    have hexp :
        saddleContourExponent a t - (j : ℂ) ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      have hpositive :
          0 < (saddleContourExponent a t - (j : ℂ)).re := by
        rw [saddleContourExponent_sub_nat_re]
        linarith
      simpa only [Complex.sub_re, saddleContourExponent_re, Complex.natCast_re, Complex.zero_re,
        ne_eq] using! hpositive.ne'
    simp only [saddlePositiveCpow, max_self, Complex.ofReal_zero, Complex.zero_cpow hexp, zero_mul]
  rw [hzero, integral_zero]

private noncomputable def SaddleSign.squaredRemainder (s : SaddleSign)
    (ε ℓ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment (saddleTaylorContour N) 0
      (fun t : ℝ =>
        s.mellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I)) u

private noncomputable def saddleSquaredResiduePolynomial
    (c : ℕ → ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    c j * ((u : ℂ) ^ j)

private theorem saddleTaylorContour_negativeHalf_pos (N : ℕ) :
    0 < -(saddleTaylorContour N) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  positivity

@[simp] private theorem saddleSquaredResiduePolynomial_zero
    (c : ℕ → ℂ) (N : ℕ) :
    saddleSquaredResiduePolynomial c N 0 = c 0 := by
  classical
  unfold saddleSquaredResiduePolynomial
  rw [Finset.sum_eq_single 0]
  · simp only [Complex.ofReal_zero, pow_zero, mul_one]
  · intro j _ hj
    simp only [Complex.ofReal_zero, zero_pow hj, mul_zero]
  · simp only [Finset.mem_range, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    not_true_eq_false,
      Complex.ofReal_zero, pow_zero, mul_one, IsEmpty.forall_iff]

@[simp] private theorem SaddleSign.squaredRemainder_zero (s : SaddleSign)
    (ε ℓ : ℝ) (N : ℕ) :
    s.squaredRemainder ε ℓ N 0 = 0 := by
  unfold SaddleSign.squaredRemainder
  rw [saddlePositiveContourMoment_zero 0
    (by simpa only [CharP.cast_eq_zero, Nat.ofNat_pos, div_pos_iff_of_pos_right,
      Left.neg_pos_iff] using! saddleTaylorContour_negativeHalf_pos N)]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    mul_zero]

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology

private noncomputable def SaddleSign.positiveSquaredContour (s : SaddleSign)
    (ε ℓ a u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment a 0
      (fun t : ℝ =>
        s.mellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) u

private noncomputable def saddleContourMomentL1
    (a : ℝ) (j : ℕ) (D : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ,
    ‖(saddleContourFallingPolynomial a j).eval
        (t : ℂ) * D t‖

private noncomputable def saddleOuterCutoff (u : ℝ) : ℂ :=
  (Real.smoothTransition (u - 2) : ℂ)

private noncomputable def SaddleSign.outerSquaredProfile (s : SaddleSign) (ε ℓ u : ℝ) : ℂ :=
  saddleOuterCutoff u *
    s.positiveSquaredContour ε ℓ 2 u

private noncomputable def saddleSquaredSchwartzPullback (d : ℕ) :
    𝓢(ℝ, ℂ) →L[ℂ] TestFunction d := by
  apply SchwartzMap.compCLM ℂ
    (Function.hasTemperateGrowth_norm_sq (Euclidean d))
  refine ⟨1, 1, ?_⟩
  intro x
  change ‖x‖ ≤ 1 * (1 + ‖‖x‖ ^ 2‖) ^ 1
  rw [one_mul, pow_one, Real.norm_of_nonneg (sq_nonneg _)]
  linarith [sq_nonneg (‖x‖ - (1 / 2 : ℝ))]

private noncomputable def saddleSourceContourEnvelopeScale
    (ε ℓ u : ℝ) : ℝ :=
  Real.exp (-(ℓ * u) * Real.log Real.pi / 2) *
    Real.Gamma (ℓ * (1 + u) / 2) *
      Real.exp (ℓ * realHyperbolicShellPhase ε u)

private noncomputable def saddleSourceContourDamping
    (ε ℓ u T : ℝ) : ℝ :=
  upperGammaDamping ℓ (1 + u) T +
    positiveShellDamping ε ℓ (u - 1) T -
      upperShortShellDamping ε ℓ (u - 1) T

private noncomputable def saddleSourceNormalizedEnvelope
    (ε ℓ u T : ℝ) : ℂ :=
  saddleMellinEnvelope ε ℓ
      (saddleSourceMellinContour ℓ u T) /
    (saddleSourceContourEnvelopeScale ε ℓ u : ℂ)

private noncomputable def saddleSourceCenteredEnvelope
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceNormalizedEnvelope ε ℓ u T *
    Complex.exp (Complex.I * ((ℓ * T * v : ℝ) : ℂ))

private noncomputable def SaddleSign.centeredIntegrand (s : SaddleSign)
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    s.polynomial ε ((T : ℂ) + Complex.I * (u : ℂ))

private noncomputable def saddleSourceCenteredPlusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  SaddleSign.centeredIntegrand .plus ε ℓ u v T

private noncomputable def saddleSourceCenteredMinusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  SaddleSign.centeredIntegrand .minus ε ℓ u v T

@[simp] private theorem saddleSourceContourDamping_eq_firstBranch
    (ε ℓ u T : ℝ) :
    saddleSourceContourDamping ε ℓ u T =
      upperFirstBranchSaddleDamping ε ℓ u T := rfl

private noncomputable def saddleSourceCenteredPrefactor
    (ε ℓ u v : ℝ) : ℝ :=
  (ℓ / (2 * Real.pi)) *
    Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u

private noncomputable def saddleSourceGaussianVariance
    (ε ℓ u : ℝ) : ℝ :=
  upperSaddleVariance ε ℓ (u - 1)

private noncomputable def saddleSourceGaussianKernel
    (ε ℓ u T : ℝ) : ℝ :=
  Real.exp
    (-(ℓ * saddleSourceGaussianVariance ε ℓ u / 2) * T ^ 2)

private noncomputable def SaddleSign.gaussianIntegrand (s : SaddleSign)
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    s.polynomial ε (Complex.I * (u : ℂ))

private noncomputable def saddleSourceGaussianPlusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  SaddleSign.gaussianIntegrand .plus ε ℓ u T

private noncomputable def saddleSourceGaussianMinusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  SaddleSign.gaussianIntegrand .minus ε ℓ u T

end

section

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

private noncomputable def upperImaginaryExp (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

private noncomputable def upperGammaCenteredKernel
    (ℓ η T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
    Complex.I * ((a * T : ℝ) : ℂ)) *
      (upperGammaMeasureDensity ℓ η a : ℂ)

private noncomputable def upperGammaCenteredPhase
    (ℓ η T : ℝ) : ℂ :=
  ∫ a : ℝ in Ioi 0, upperGammaCenteredKernel ℓ η T a

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private noncomputable def saddleSourceCosineQuadraticRemainder
    (a u T : ℝ) : ℂ :=
  Complex.cos
      ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) -
    (Real.cosh (u * a) : ℂ) +
    Complex.I * ((a * T * Real.sinh (u * a) : ℝ) : ℂ) +
    ((a ^ 2 * T ^ 2 / 2 * Real.cosh (u * a) : ℝ) : ℂ)

private noncomputable def saddleSourceShellCenteredPhase
    (ε ℓ u T : ℝ) : ℂ :=
  (ℓ : ℂ) *
    (mellinShellPhase ε
        ((T : ℂ) + Complex.I * (u : ℂ)) -
      (realHyperbolicShellPhase ε u : ℂ) +
      Complex.I *
        ((T * saddleSourceShellDerivative ε u : ℝ) : ℂ))

private noncomputable def saddleSourceShellQuadraticRemainder
    (ε u T : ℝ) : ℂ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (shortShellDensity ε a : ℂ) *
      saddleSourceCosineQuadraticRemainder a u T) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    (positiveShellDensity ε a : ℂ) *
      saddleSourceCosineQuadraticRemainder a u T)

end

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def upperGammaQuadraticKernel
    (ℓ η T a : ℝ) : ℂ :=
  (((a * T) ^ 2 / 2 *
    upperGammaMeasureDensity ℓ η a : ℝ) : ℂ)

private noncomputable def upperGammaCubicRemainderKernel
    (ℓ η T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
    Complex.I * ((a * T : ℝ) : ℂ) +
      (((a * T) ^ 2 / 2 : ℝ) : ℂ)) *
        (upperGammaMeasureDensity ℓ η a : ℂ)

end
end CohnElkies
