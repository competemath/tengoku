/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# unique extension criterion

Valuations are regarded valuations up to equivalence.  Accordingly, uniqueness on
an algebraic extension is stated as literal uniqueness of its valuation
subring.  This is the same endpoint used in the finite norm-formula theorem.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u

/-- A valuation subring has a unique extension valuation ring to `L`.-/
def HasUniqueValuationSubringExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) : Prop :=
  ∃! W : ValuationSubring L, V.valuation.HasExtension W.valuation

/-- A valuation subring has a unique extension valuation ring on every
algebraic extension in the same universe.  This is the valuation-ring form
of the right-hand side of the unique-extension criterion.-/
def HasUniqueAlgebraicValuationSubringExtensions
    {K : Type u} [Field K] (V : ValuationSubring K) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L],
    HasUniqueValuationSubringExtension (L := L) V

end Valuations
end AlgebraicNumberTheory

end
