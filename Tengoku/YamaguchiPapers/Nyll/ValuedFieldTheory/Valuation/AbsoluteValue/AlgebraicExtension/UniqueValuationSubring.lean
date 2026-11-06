/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# uniqueness from the integral-closure valuation ring

Once the actual integral closure of a valuation subring satisfies the
valuative dichotomy, it is contained in every extension valuation ring.  Its
integrality over the base then forces the center of every such overring to be
the unique maximal ideal, so the overring is the integral closure itself.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField.Valuation

namespace Valuation

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

end Valuation
end DiscreteValuationField

end
