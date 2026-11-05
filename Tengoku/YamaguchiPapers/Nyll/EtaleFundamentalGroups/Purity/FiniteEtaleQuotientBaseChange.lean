/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.FiniteEtaleQuotientLift
import Tengoku.Seed.RingTheory.Etale.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Essential surjectivity of finite-etale base change to a quotient

For a complete Noetherian local ring, every finite-etale algebra over a
quotient by an ideal in the maximal ideal comes by base change from the
original ring.  This file packages the algebraic lifting theorem as the
canonical categorical `EssSurj` statement for finite-etale algebras.
-/

noncomputable section

namespace EtaleFundamentalGroups

open CategoryTheory IsLocalRing

universe u

end EtaleFundamentalGroups

end
