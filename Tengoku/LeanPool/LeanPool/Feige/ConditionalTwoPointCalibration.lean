/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.AugmentedParameterization
import Tengoku.LeanPool.LeanPool.Feige.ConditionalProductKernel
import Tengoku.LeanPool.LeanPool.Feige.TwoPointProductLaw

/-!
# Conditional calibration of augmented two-point products

The finite combinatorial theorem is isolated as a reusable proposition.
Once it is available (including boundary values `γᵢ = 0`), the actual
conditional product law selected by any admissible augmented latent vector
inherits the same rejection bound.
-/

@[expose] public section

open MeasureTheory

namespace Feige

noncomputable section

/-- The finite two-point rejection estimate needed by the mixture
argument, including the closed boundary `0 ≤ γᵢ ≤ 1`. -/
def TwoPointRejectionBound : Prop :=
  ∀ {m : ℕ} (γ β : Fin m → ℝ),
    (∀ i, 0 ≤ γ i) →
    (∀ i, γ i ≤ 1) →
    (∀ i, 0 < β i) →
    ∀ {α : ℝ}, 0 ≤ α →
      twoPointRejectionMass γ β α ≤ α

end

end Feige
