/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.GradedCycles
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Codimension of the pushforward to the spectrum of a field

For a quasi-compact `f : X ⟶ Spec K` over a field with `dim X ≤ n`, the ungraded cycle pushforward
`AlgebraicCycle.pushforward f D (fun _ ↦ ()) (fun _ ↦ ())` of a codimension-`p` cycle is a
codimension-`(p - n)` cycle (natural subtraction).  Applied to `ℙⁿ_k → Spec k` this is the
blueprint leaf `ChowOperations.pushPi_homog` (`pushforward_toSpec_mem_codimensionCycles`).

The content is dimension-theoretic only: every point of `Spec K` has codimension `0`, and a
codimension-`p` cycle on `X` vanishes unless `p ≤ n`, in which case `p - n = 0`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Order

universe u

namespace AlgebraicGeometry.Chow

variable {X Y : Scheme.{u}}

/-- Every point of the spectrum of a field has codimension `0`.-/
theorem coheight_spec_field (K : Type u) [Field K] (y : Spec (CommRingCat.of K)) :
    coheight y = 0 := by
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact coheight_eq_zero.mpr fun b _ ↦ (Subsingleton.elim b y).le

end AlgebraicGeometry.Chow
