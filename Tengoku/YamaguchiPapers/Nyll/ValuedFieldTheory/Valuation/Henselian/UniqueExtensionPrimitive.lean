/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import Tengoku.Seed.GroupTheory.OrderOfElement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# primitive irreducible reductions

This file supplies the last Galois/Newton-polygon input in the converse of
the unique-extension criterion.  Uniqueness of the extension valuation ring makes it invariant
under the finite Galois group of a splitting field.  Consequently conjugate
roots have the same value.  Vieta's formulas then show that a primitive
irreducible polynomial has either full-degree reduction or constant
reduction; in the full-degree case the monic normalization has no coprime
nonconstant residual factorization.
-/

noncomputable section

open Polynomial

namespace AlgebraicNumberTheory
namespace Valuations
open ValuationTheory.Valuations

universe u

end Valuations
end AlgebraicNumberTheory

end
