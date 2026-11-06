/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coefficient norm of an irreducible polynomial

The nonarchimedean valuation construction supplies the irreducible coefficient estimate.

The unique nonarchimedean extension to a splitting field is invariant under
all ground-field automorphisms.  Normality of a splitting field therefore
forces all conjugate roots of an irreducible polynomial to have one common
absolute value.  Vieta's factorization and the strong triangle inequality
then bound every coefficient by the larger endpoint coefficient.
-/

noncomputable section

open Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- The hypothesis that `w` is the unique nonarchimedean exact
extension of `v` to `L`.-/
def IsUniqueNonarchimedeanAbsoluteValueExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Prop :=
  LubinTate.Valuations.NonarchimedeanAbsoluteValue w ∧ AbsoluteValue.Extends v w ∧
    ∀ u : AbsoluteValue L ℝ,
      LubinTate.Valuations.NonarchimedeanAbsoluteValue u → AbsoluteValue.Extends v u → u = w

end Valuations
end AlgebraicNumberTheory

end
