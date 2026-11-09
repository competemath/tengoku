/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Standard open subgroups of a nonarchimedean local field

An open finite-index subgroup of a nonarchimedean local field multiplicative group
contains a standard subgroup built from a uniformizer and a sufficiently deep
principal-unit group.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

universe u

/-- The `n`-th principal-unit group, viewed as a subgroup of the field's
multiplicative group.-/
def fieldPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] (n : ℕ) : Subgroup Kˣ :=
  (principalUnits K n).map (integerUnitsToFieldUnits K)

/-- The standard subgroup `(ϖ^d) · U^n` used in the existence theorem.
The product of the two commuting subgroups is written as their supremum.-/
def uniformizerPrincipalSubgroup
    (K : Type u) [Field K] [ValuativeRel K]
    (ϖ : Kˣ) (d n : ℕ) : Subgroup Kˣ :=
  Subgroup.zpowers (ϖ ^ d) ⊔ fieldPrincipalUnits K n

end LocalFieldTheory

end
