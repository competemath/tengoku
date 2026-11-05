/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Etale.Locus
import Tengoku.Seed.RingTheory.Ideal.Height
import Tengoku.Seed.RingTheory.IntegralClosure.GoingDown

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The codimension-one support input to special local purity

This file isolates the part of special local purity currently supported by
the commutative-algebra API.  In a faithfully integral extension of domains
over an integrally closed base, going-down and incomparability identify the
height of a prime with the height of its contraction.  Consequently, if the
extension is unramified (respectively etale) over every height-one base
prime, the support of relative differentials (respectively the union with
the first cotangent homology support) contains no height-one prime.

The missing step to full purity is precisely the codimension-at-least-two
support-vanishing theorem; it is not assumed here.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v

end EtaleFundamentalGroups.SpecialLocalPurity

end
