/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.SharpnessData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The classification of arithmetic (and coreless) `(1;∞)`-groups

For `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2`, write `IsTakeuchiConj A B` for: some
Nielsen-equivalent generating pair `(A', B')` of `⟨A, B⟩` is, up to signs, simultaneously
`GL(2, ℝ)`-conjugate to one of the four explicit pairs `takeuchiPair i`.

* `isArithmeticSL_iff_isTakeuchiConj`: `⟨A, B⟩` is arithmetic iff `IsTakeuchiConj A B`. This is
  Takeuchi's theorem ([Take2] Thm. 4.1(i), `e = ∞`), fully proved.
* `not_admitsCore_of_isTakeuchiConj`: the four groups admit no core (unconditional).
* `not_admitsCore_iff_isTakeuchiConj`: assuming `MargulisOneInfty`, `⟨A, B⟩` admits no core iff
  `IsTakeuchiConj A B`. This is the group-theoretic form of [CanLift] Prop. 2.7 /
  [EstIUT] Prop. 2.1: the coreless once-punctured tori are exactly the four arithmetic ones.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

/-- `⟨A, B⟩` has a Nielsen-equivalent generating pair which, up to signs, is simultaneously
`GL(2, ℝ)`-conjugate to one of Takeuchi's four pairs. -/
def IsTakeuchiConj (A B : SL(2, ℝ)) : Prop :=
  ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
    ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
      ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
        g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2

end OrbicurveCores
