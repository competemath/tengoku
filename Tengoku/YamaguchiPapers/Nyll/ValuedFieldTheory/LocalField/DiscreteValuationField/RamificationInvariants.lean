/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= 1`.
@isnad1 id=iff.0h4v.s6.c1cbe59d8218 from=translated src=- shape=161dadc4 vocab=85452ea2
-/
@[simp] theorem isUnramified_iff_ramificationIndex_eq_one :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF = 1 :=
  Iff.rfl

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF =
1`.
@isnad1 id=iff.0h4v.s6.b87a0592584b from=translated src=- shape=161dadc4 vocab=74fc673d
-/
@[simp] theorem isTotallyRamified_iff_residueDegree_eq_one :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF = 1 :=
  Iff.rfl

variable [FiniteDimensional K L]

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
