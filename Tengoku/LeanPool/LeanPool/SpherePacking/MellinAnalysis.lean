/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all Tengoku.LeanPool.LeanPool.SpherePacking.Foundations
public import Tengoku
import Tengoku

/-!
# MellinAnalysis

Mellin inversion and lower-contour estimates.
-/

namespace CohnElkies

section

open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology

private noncomputable def saddleMellinInversePowerPoleSlope
    (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  dslope (saddleMellinInversePower r)
    (-((2 * n : ℕ) : ℂ)) z

private noncomputable def saddleGaussianPoleWeightedCorrection
    (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2) *
    saddleMellinInversePowerPoleSlope r n z

private noncomputable def saddleTaylorContour (N : ℕ) : ℝ :=
  -((2 * N + 1 : ℕ) : ℝ)

private noncomputable def plusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))

private noncomputable def minusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))

end

section

open Filter
open scoped Topology

end

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def frullaniKernel (a b x : ℝ) : ℝ :=
  (Real.exp (-a * x) - Real.exp (-b * x)) / x

private noncomputable def wallisPairKernel (n : ℕ) (x : ℝ) : ℝ :=
  frullaniKernel (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2) x -
    frullaniKernel (2 * (n : ℝ) + 2) (2 * (n : ℝ) + 3) x

private noncomputable def wallisPairFactor (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) *
    ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))

private noncomputable def wallisPartialKernel (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, wallisPairKernel k x

private noncomputable def wallisLaplaceKernel (x : ℝ) : ℝ :=
  Real.exp (-x) * (1 - Real.exp (-x)) /
    (x * (1 + Real.exp (-x)))

end

section

open Filter MeasureTheory
open scoped Topology

private noncomputable def shellRadiusMajorant (ε : ℝ) : ℝ :=
  ((ε⁻¹ ^ 3) + 1) * shellWeight ε *
    Real.exp ((ε / 4) * ((ε⁻¹ ^ 3) + 1))

private noncomputable def shortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  shortShellDensity ε a * a * Real.sinh ((1 + ε / 4) * a)

private noncomputable def wallisRadiusIntegrand (a : ℝ) : ℝ :=
  -(Real.exp (-2 * a) * Real.tanh a / (2 * a))

private noncomputable def shortShellRadiusMajorant (a : ℝ) : ℝ :=
  7 * Real.exp (-(3 / 4 : ℝ) * a)

private noncomputable def shortShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellRadiusIntegrand ε a

private noncomputable def supportedShortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  (Set.Ioc (ε ^ 3) (10 * Real.log (1 / ε))).indicator
    (shortShellRadiusIntegrand ε) a

private noncomputable def limitingSaddleRadius (ε : ℝ) : ℝ :=
  Real.sqrt ((2 + ε / 4) / (4 * Real.pi)) *
    Real.exp (shortShellRadiusContribution ε +
      positiveShellRadiusContribution ε)

end

section

open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

private noncomputable def radialL1Mass {d : ℕ} (g : TestFunction d) : ℝ :=
  ∫ x : Euclidean d, ‖g x‖

private noncomputable def normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) : ℝ :=
  radialSurfaceArea d / radialL1Mass g *
    (R * Real.exp v) ^ d *
    (radialProfile hd g (R * Real.exp v)).re

end

section

open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def radialLineIsometry {d : ℕ} (hd : 0 < d) :
    ℝ →ₗᵢ[ℝ] Euclidean d :=
  LinearIsometry.toSpanSingleton ℝ (Euclidean d)
    (norm_radialUnitDirection hd)

private noncomputable def radialSchwartzProfile {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (radialLineIsometry hd).toContinuousLinearMap.hasTemperateGrowth
    (radialLineIsometry hd).isometry.antilipschitzWith f

@[simp] private theorem radialSchwartzProfile_apply {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (r : ℝ) :
    radialSchwartzProfile hd f r = radialProfile hd f r := by
  rfl

private noncomputable def radialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (z : ℂ) : ℂ :=
  mellin (radialProfile hd f)
    ((d : ℂ) / 2 - Complex.I * z)

private noncomputable def normalizedRadialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (R : ℝ) (z : ℂ) : ℂ :=
  (radialSurfaceArea d / radialL1Mass f : ℝ) *
    Complex.exp
      (((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ)) *
      radialMellinStrip hd f z

private noncomputable def schwartzExponentialTilt
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) : ℂ :=
  (Real.exp (κ * v) : ℂ) * g (R * Real.exp v)

end

section

private noncomputable def stripAngle (σ : ℝ) : ℝ :=
  Real.pi * (1 + σ) / 2

private noncomputable def stripPoissonKernel (σ T : ℝ) : ℝ :=
  Real.sin (stripAngle σ) /
    (4 * (Real.cosh (Real.pi * T / 2) - Real.cos (stripAngle σ)))

private noncomputable def stripBottomMass (σ : ℝ) : ℝ :=
  (1 - σ) / 2

end

section

open Filter MeasureTheory Set
open scoped Interval Topology

private noncomputable def stripPoissonPrimitive (σ T : ℝ) : ℝ :=
  Real.arctan
      ((Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
        Real.sin (stripAngle σ)) / Real.pi

private noncomputable def stripComplexPoissonKernel (σ T : ℝ) : ℂ :=
  Complex.I *
      ((Complex.exp
          (((Real.pi * T / 2 : ℝ) : ℂ) +
            Complex.I * ((stripAngle σ : ℝ) : ℂ)) + 1) /
        (Complex.exp
          (((Real.pi * T / 2 : ℝ) : ℂ) +
            Complex.I * ((stripAngle σ : ℝ) : ℂ)) - 1)) /
    4

private noncomputable def stripSchwarzExponential (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp
    (((Real.pi : ℂ) *
      (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
        (2 * (ℓ : ℂ)))

private noncomputable def stripHolomorphicPoissonKernel (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (Complex.I *
      ((Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) + 1) /
        (Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) - 1)) /
    4) / (ℓ : ℂ)

private noncomputable def stripRegularizedHolomorphicPoissonKernel
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  stripHolomorphicPoissonKernel ℓ z y +
    (if 0 ≤ y then Complex.I else -Complex.I) /
      ((4 * ℓ : ℝ) : ℂ)

private noncomputable def stripRegularizedHolomorphicPoissonKernelDeriv
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  -(Complex.I * (Real.pi : ℂ) *
      stripSchwarzExponential ℓ z y) /
    (4 * (ℓ : ℂ) ^ 2 *
      (stripSchwarzExponential ℓ z y - 1) ^ 2)

end

section

open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology

private noncomputable def profileNegativePart (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  max (-φ v) 0

private noncomputable def lowerGammaBoundaryLog (ℓ R y : ℝ) : ℝ :=
  ℓ * Real.log (Real.pi * R ^ 2) +
    Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
    Real.log ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖

private noncomputable def lowerStripPoissonMajorant (ℓ R σ s : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T *
      lowerGammaBoundaryLog ℓ R (s - ℓ * T)

private noncomputable def lowerCoth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

private noncomputable def lowerGammaScaledPositivePart
    (d : ℕ) (c Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) 0

private noncomputable def lowerRiemannLog (T x : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + T ^ 2 / 4))

private noncomputable def lowerEndpointPhase (T : ℝ) : ℝ :=
  -Real.pi * |T| / 4 - (1 / 2 : ℝ) * Real.log (1 + T ^ 2 / 4) +
    |T| / 2 * Real.arctan (|T| / 2)

private noncomputable def lowerRiemannLogPrimitive (T x : ℝ) : ℝ :=
  x / 2 * Real.log (x ^ 2 + T ^ 2 / 4) - x +
    (|T| / 2) * Real.arctan (x / (|T| / 2))

end
end CohnElkies
