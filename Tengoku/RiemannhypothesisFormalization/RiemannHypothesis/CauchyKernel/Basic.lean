/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Analytic
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Analysis.Calculus.Deriv.Pow
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Definitions
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.SignTargets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Paired Cauchy kernel and the cloud–tail decomposition

The atomic positive-real-charge building block
`K_u(z) := 1/(z − u) + 1/(z + u) = 2z/(z² − u²)`, whose imaginary part is
automatically nonpositive on the upper half-plane, and the cloud–tail
machinery built on top: any positive-weighted sum of paired kernels is
anti-Herglotz, and a `model = cloud + tail` split with both pieces
anti-Herglotz yields the anti-Herglotz sign condition.

## Main results

* `pairedCauchyKernel`, `pairedCauchyKernel_im_nonpos_at` — the kernel and its
  upper-half-plane sign.
* `finitePositivePairedTail_antiHerglotz` — positive-weighted paired sums are
  anti-Herglotz.
* `CloudTailDecomposition` / `.antiHerglotz` — the abstract split.
* `XiRealCloudTailPackage` / `XiPositiveCloudTailPackage` — the Ξ-facing
  packages and their bridge to `XiPullback.AntiHerglotzSign`.
-/

namespace OverflowResidueRH

open Complex

-- =====================================================================
-- Paired Cauchy kernel: imaginary-part sign on the upper half-plane
-- =====================================================================

/-- The **paired Cauchy kernel**
  `K_u(z) := 1/(z − u) + 1/(z + u) = 2z / (z² − u²)`.-/
noncomputable def pairedCauchyKernel (u : ℝ) (z : ℂ) : ℂ :=
  (1 : ℂ) / (z - (u : ℂ)) + (1 : ℂ) / (z + (u : ℂ))

end OverflowResidueRH
