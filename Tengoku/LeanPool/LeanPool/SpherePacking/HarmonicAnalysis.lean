/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all Tengoku.LeanPool.LeanPool.SpherePacking.SaddleAnalysis
public import Tengoku

/-!
# HarmonicAnalysis

Harmonic majorization and quantitative asymptotic estimates.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private noncomputable def upperCenteredLaplaceKernel
    (c T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
      Complex.I * ((a * T : ℝ) : ℂ)) *
    ((Real.exp (-c * a) / a : ℝ) : ℂ)

private noncomputable def upperGammaCenteredTruncatedKernel
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  upperCenteredLaplaceKernel η T a *
    ((∑ k ∈ Finset.range (n + 1),
      Real.exp (-(2 * a / ℓ)) ^ k : ℝ) : ℂ)

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private noncomputable def saddleSourceStationaryLogRadius
    (ε ℓ u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (ℓ * (1 + u) / 2) / 2 +
      saddleSourceShellDerivative ε u

private noncomputable def saddleSourceCenteredPhase
    (ε ℓ u T : ℝ) : ℂ :=
  upperGammaCenteredPhase ℓ (1 + u) T +
    saddleSourceShellCenteredPhase ε ℓ u T

private noncomputable def saddleSourceGaussianPhaseRemainder
    (ε ℓ u T : ℝ) : ℂ :=
  saddleSourceCenteredPhase ε ℓ u T +
    ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
      T ^ 2 : ℝ) : ℂ)

end

section

open Filter MeasureTheory Set
open scoped Topology

end

section

open Filter Set MeasureTheory
open scoped Topology

private noncomputable def saddleGaussianTailWeight (T : ℝ) : ℝ :=
  1 + |T| ^ 3

private noncomputable def saddleGaussianTailSet (R : ℝ) : Set ℝ :=
  {T : ℝ | R ≤ |T|}

private noncomputable def saddleGaussianOuterPhi
    (B Q c ℓ δ : ℝ) : ℝ :=
  (B + 1) / 2 * δ + 4 * Real.log (2 + δ) -
    c * ℓ * Q * Real.exp (B * δ)

private noncomputable def saddleSourceFirstBranchVarianceCoefficient
    (ε : ℝ) : ℝ :=
  (3 / 2 : ℝ) +
    (2 + ε / 2) *
      upperPositiveShellVariance ε (ε / 2)

private noncomputable def saddleFirstBranchTailLogMajorant
    (c C ℓ : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * C / c) *
      Real.exp
        (-(c / (4 * C)) *
          (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) +
    (16 / c) *
      Real.sqrt (C / (Real.log ℓ / 4))

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private noncomputable def saddleSourceFirstBranchThirdMomentCoefficient
    (ε : ℝ) : ℝ :=
  (5 / 2 : ℝ) +
    (3 / 2 : ℝ) * (10 * Real.log (1 / ε)) * (2 + ε / 2) +
    (2 + ε / 2) ^ 2 *
      upperPositiveShellThirdMoment ε (ε / 2)

private noncomputable def saddleSourceSecondBranchVarianceFloor (ε : ℝ) : ℝ :=
  (99 / 200 : ℝ) * (ε⁻¹ ^ 3) ^ 2 *
    shellWeight ε *
      Real.exp ((ε / 2) * (ε⁻¹ ^ 3))

end

section

open Filter Set
open scoped Topology

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private noncomputable def saddleSourceFirstBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  (ℓ * (1 + u)) ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)

private noncomputable def saddleSourceSecondBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  ℓ ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)

private noncomputable def saddleSourceSecondBranchLocalFrequency (ε : ℝ) : ℝ :=
  1 / (2 * ((ε⁻¹ ^ 3) + 1))

private noncomputable def saddleSourceSecondBranchGaussianRate
    (ε ℓ δ : ℝ) : ℝ :=
  (ℓ / (100 * Real.exp 1)) *
    saddleSourceGaussianVariance ε ℓ (1 + δ)

private noncomputable def saddleSourceSecondBranchGammaGaussianRate
    (ℓ δ : ℝ) : ℝ :=
  (ℓ / (8 * Real.exp 1)) / (2 + δ)

private noncomputable def saddleSourceSecondBranchGammaLinearRate
    (ℓ : ℝ) : ℝ :=
  ℓ / (8 * Real.exp 1)

private noncomputable def saddleSourceSecondBranchOuterBarrier
    (ε ℓ δ : ℝ) : ℝ :=
  (99 / 5000 : ℝ) * ℓ * shellWeight ε *
    Real.exp (δ * (ε⁻¹ ^ 3)) *
      saddleSourceSecondBranchLocalFrequency ε ^ 2

private noncomputable def saddleSourceSecondBranchMomentCoefficient : ℝ :=
  let C : ℝ := 8 * Real.exp 1
  2 * (1 + (6 * C) ^ 3) *
      (1 + 2 * Real.pi * C) +
    8 * C * (1 + (6 * C) ^ 3)

private noncomputable def saddleSourceSecondBranchVarianceCoefficient (ε : ℝ) : ℝ :=
  2 + ((ε⁻¹ ^ 3) + 1) ^ 2 * shellWeight ε

end

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def saddleSourceGaussianNormalizedTailMajorant (x : ℝ) : ℝ :=
  4 * Real.sqrt (2 * Real.pi) *
    Real.exp (-(x ^ (1 / 6 : ℝ)) / 8)

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

end

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

end

section

open Filter
open scoped Topology

private noncomputable def EventualLowerBound : Prop :=
  ∀ c : ℝ, c < Real.pi⁻¹ →
    ∀ᶠ d : ℕ in atTop, c ≤ normalizedProgram d

private noncomputable def EventualUpperBound : Prop :=
  ∀ c : ℝ, Real.pi⁻¹ < c →
    ∀ᶠ d : ℕ in atTop, normalizedProgram d ≤ c

private noncomputable def UniformAdmissibleLowerBound : Prop :=
  ∀ c : ℝ, c < Real.pi⁻¹ →
    ∀ᶠ d : ℕ in atTop,
      ∀ f : Admissible d, c ≤ normalizedCost f

private noncomputable def ConstructivePrimalUpperBound : Prop :=
  ∀ c : ℝ, Real.pi⁻¹ < c →
    ∀ᶠ d : ℕ in atTop,
      ∃ f : Admissible d, normalizedCost f ≤ c

private structure OrderedEpsilonUpperConstruction where
  epsilonBound : ℝ
  epsilonBound_pos : 0 < epsilonBound
  normalizedRadius : ℝ → ℕ → ℝ
  limitingRadius : ℝ → ℝ
  limitingRadius_tendsto :
    Tendsto limitingRadius (𝓝[>] (0 : ℝ)) (𝓝 Real.pi⁻¹)
  normalizedRadius_tendsto :
    ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      Tendsto (normalizedRadius ε) atTop (𝓝 (limitingRadius ε))
  admissibleWitness :
    ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      ∀ᶠ d : ℕ in atTop,
        ∃ f : Admissible d, normalizedCost f ≤ normalizedRadius ε d

end
end CohnElkies
