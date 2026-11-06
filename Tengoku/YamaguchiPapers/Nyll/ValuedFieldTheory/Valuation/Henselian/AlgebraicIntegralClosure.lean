/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.SimpleRootFactorization
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral closures of Henselian valuation rings

In an algebraic extension, every element or its inverse is integral over a
Henselian valuation ring. The argument extends the valuation to an algebraic
closure, uses equality of the values of conjugate roots, and bounds the
coefficients of the minimal polynomial by the nonarchimedean Vieta bound.
No restriction on the rank or value group is imposed.
-/

namespace ValuationTheory.Henselian

end ValuationTheory.Henselian
