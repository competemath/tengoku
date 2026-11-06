/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Unramified.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Henselianity along algebraic valued extensions

The proof of the unramified base-change theorem applies Hensel's lemma after
base change from `K` to an algebraic extension `K'`.  This file supplies the
source used there: the unique extension of a Henselian valuation to an
algebraic field is again Henselian.  The result is derived from the unique
extension criterion of the unique-extension criterion, rather than added as an assumption to
the unramified base-change theorem.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u

end Valuations
end AlgebraicNumberTheory

end
