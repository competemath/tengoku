/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all Tengoku.LeanPool.LeanPool.SpherePacking.MellinAnalysis
public import Tengoku
import Tengoku

/-!
# GammaAnalysis

Gamma-kernel estimates and radial asymptotics.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def complexFrullaniSegment (z w : ℂ) (s : ℝ) : ℂ :=
  z + (s : ℂ) * (w - z)

private noncomputable def complexFrullaniKernel (z w : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-z * (x : ℂ)) -
    Complex.exp (-w * (x : ℂ))) / (x : ℂ)

private noncomputable def complexWallisPhaseKernel (z : ℂ) (x : ℝ) : ℂ :=
  ((1 - Complex.exp (-(x : ℂ))) *
      Complex.exp (-z * (x : ℂ)) -
    (x : ℂ) * Complex.exp (-(x : ℂ))) /
      (x : ℂ) ^ 2

end

section

open Filter MeasureTheory Set
open scoped Interval Topology

private noncomputable def stripNormalizedPoissonKernel (σ T : ℝ) : ℝ :=
  stripPoissonKernel σ T / stripBottomMass σ

private noncomputable def stripNormalizedPoissonExtension (σ T : ℝ) : ℝ :=
  (Real.pi / 4) *
    Real.sinc (Real.pi * (1 - σ) / 2) /
      (Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - σ) / 2))

private noncomputable def limitingStripPoissonDensity (T : ℝ) : ℝ :=
  Real.pi /
    (4 * (Real.cosh (Real.pi * T / 2) + 1))

private noncomputable def stripPoissonExponentialMajorant (T : ℝ) : ℝ :=
  (Real.pi / 2) *
    Real.exp (-(Real.pi / 2) * |T|)

private noncomputable def poissonLogistic (u : ℝ) : ℝ :=
  Real.exp (Real.pi * u) /
    (1 + Real.exp (Real.pi * u))

private noncomputable def poissonLogisticDensity (u : ℝ) : ℝ :=
  Real.pi * Real.exp (Real.pi * u) /
    (1 + Real.exp (Real.pi * u)) ^ 2

private noncomputable def lowerPoissonEndpointExpectation (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripNormalizedPoissonKernel σ T * lowerEndpointPhase T

private noncomputable def limitingPoissonEndpointExpectation : ℝ :=
  ∫ T : ℝ,
    limitingStripPoissonDensity T * lowerEndpointPhase T

private noncomputable def lowerWallisPhaseKernel (u t : ℝ) : ℝ :=
  ((1 - Real.exp (-t)) * Real.cos (u * t) -
    t * Real.exp (-t)) / t ^ 2

private noncomputable def lowerWallisRegularizedPhaseKernel (a u t : ℝ) : ℝ :=
  ((1 - Real.exp (-t)) * Real.exp (-a * t) *
      Real.cos (u * t) - t * Real.exp (-t)) / t ^ 2

private noncomputable def lowerWallisRegularizedPhaseMajorant (u t : ℝ) : ℝ :=
  if t ≤ 1 then |u| + 2 else 1 / t ^ 2 + Real.exp (-t)

private noncomputable def lowerWallisComplexLogPhase (z : ℂ) : ℝ :=
  (1 + z * Complex.log z -
    (z + 1) * Complex.log (z + 1)).re

end

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def upperNegativeHalfGammaArgument (N : ℕ) (s : ℝ) : ℂ :=
  -((N : ℂ) + (1 / 2 : ℂ)) -
    Complex.I * ((s / 2 : ℝ) : ℂ)

private noncomputable def upperShellShortCoefficient (ε : ℝ) : ℝ :=
  (10 * Real.log (1 / ε)) + (ε ^ 3)⁻¹

private noncomputable def upperShellMarginRatio (ε : ℝ) : ℝ :=
  5000 * upperShellShortCoefficient ε *
      Real.exp ((ε / 2) * (10 * Real.log (1 / ε))) /
    (shellWeight ε *
      Real.exp ((ε / 2) * (ε⁻¹ ^ 3)))

private noncomputable def upperShortShellDamping (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (-shortShellDensity ε a) *
      Real.cosh ((1 + δ) * a) *
        (1 - Real.cos (a * T))

private noncomputable def upperPositiveShellVariance (ε δ : ℝ) : ℝ :=
  ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a ^ 2 *
      Real.cosh ((1 + δ) * a)

private noncomputable def upperShortShellVariance (ε δ : ℝ) : ℝ :=
  ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (-shortShellDensity ε a) * a ^ 2 *
      Real.cosh ((1 + δ) * a)

private noncomputable def upperNetShellVariance (ε δ : ℝ) : ℝ :=
  upperPositiveShellVariance ε δ -
    upperShortShellVariance ε δ

private noncomputable def upperPositiveShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a ^ 3 *
      Real.cosh ((1 + δ) * a)

private noncomputable def upperShortShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (-shortShellDensity ε a) * a ^ 3 *
      Real.cosh ((1 + δ) * a)

private noncomputable def upperNetShellThirdMoment (ε δ : ℝ) : ℝ :=
  upperPositiveShellThirdMoment ε δ +
    upperShortShellThirdMoment ε δ

private noncomputable def upperGammaMeasureDensity (ℓ η a : ℝ) : ℝ :=
  Real.exp (-η * a) /
    (a * (1 - Real.exp (-(2 * a / ℓ))))

private noncomputable def upperGammaVariance (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 2 * upperGammaMeasureDensity ℓ η a

private noncomputable def upperGammaThirdMoment (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 3 * upperGammaMeasureDensity ℓ η a

private noncomputable def saddleShellDerivativeOne (ε : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * a * Real.sinh a) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a * Real.sinh a)

private noncomputable def saddleSmallRadiusVariable (ε r : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) * r ^ 2

private noncomputable def plusSaddleSmallRadiusCoefficient
    (ε ℓ : ℝ) (n : ℕ) : ℝ :=
  Real.exp
      (ℓ *
        (realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ) -
            realHyperbolicShellPhase ε 1) -
        2 * (n : ℝ) * saddleShellDerivativeOne ε) *
    (((ε / 4) - (2 * (n : ℝ) / ℓ) *
        (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
      (ε / 4))

private noncomputable def upperGammaDampingIntegrand (ℓ η T a : ℝ) : ℝ :=
  (1 - Real.cos (a * T)) *
    upperGammaMeasureDensity ℓ η a

private noncomputable def upperGammaDamping (ℓ η T : ℝ) : ℝ :=
  ∫ a : ℝ in Ioi 0,
    upperGammaDampingIntegrand ℓ η T a

private noncomputable def upperSaddleDamping (ε ℓ δ T : ℝ) : ℝ :=
  upperGammaDamping ℓ (2 + δ) T +
    positiveShellDamping ε ℓ δ T -
      upperShortShellDamping ε ℓ δ T

private noncomputable def upperSaddleVariance (ε ℓ δ : ℝ) : ℝ :=
  upperGammaVariance ℓ (2 + δ) +
    upperNetShellVariance ε δ

private noncomputable def upperSaddleThirdMoment (ε ℓ δ : ℝ) : ℝ :=
  upperGammaThirdMoment ℓ (2 + δ) +
    upperNetShellThirdMoment ε δ

private noncomputable def upperSaddleShellThirdCoefficient (ε : ℝ) : ℝ :=
  (ε⁻¹ ^ 3) + 1 + (10 * Real.log (1 / ε)) / 100

private noncomputable def upperFirstBranchSaddleDamping
    (ε ℓ u T : ℝ) : ℝ :=
  upperGammaDamping ℓ (1 + u) T +
    positiveShellDamping ε ℓ (u - 1) T -
      upperShortShellDamping ε ℓ (u - 1) T

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def radialCriticalLogProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (u : ℝ) : ℂ :=
  Real.exp (-((d : ℝ) / 2) * u) •
    radialProfile hd f (Real.exp (-u))

private noncomputable def saddleDigamma (x : ℝ) : ℝ :=
  deriv (Real.log ∘ Real.Gamma) x

private noncomputable def saddleLogRadius (ε : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
    (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
      shortShellDensity ε a * a * Real.sinh (u * a)) +
    (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
      positiveShellDensity ε a * a * Real.sinh (u * a))

private noncomputable def saddleSourceRadius (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp (saddleLogRadius ε d (1 + ε / 4))

private noncomputable def saddleCriticalGammaArgument (ε : ℝ) (d : ℕ) : ℝ :=
  ((d : ℝ) / 2) * (2 + ε / 4) / 2

end
end CohnElkies
