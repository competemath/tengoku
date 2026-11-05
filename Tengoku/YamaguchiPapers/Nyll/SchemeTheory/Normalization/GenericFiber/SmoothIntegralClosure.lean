/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Smooth.IntegralClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral elements in a smooth generic fibre

Let `R` be a normal domain with fraction field `K`, and let `S / R` be
smooth.  Every element of `S ⊗[R] K` which is integral over `S` already
comes from `S`.

This is the elementwise form of smooth base change for integral closure.  It
is useful for finite-etale generic fibres: primitive idempotents and elements
supported on a selected field component are integral, hence descend to the
original finite-etale algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uS uK

end EtaleFundamentalGroups

end
