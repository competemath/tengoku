/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicIntegralClosure
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness over an algebraic extension of a Henselian valued field

The integral closure is an actual valuation ring. Every extension valuation
has this ring of integers, so any two extension valuations are equivalent.
-/

namespace ValuationTheory.Henselian

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  (V : ValuationSubring K) [HenselianRing V (IsLocalRing.maximalIdeal V)]

end ValuationTheory.Henselian
