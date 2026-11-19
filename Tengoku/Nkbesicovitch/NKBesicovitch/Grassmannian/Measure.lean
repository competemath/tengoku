/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Topology
public import Tengoku.Seed.MeasureTheory.Measure.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The natural probability measure on the real Grassmannian

Push forward normalized Haar measure along an orbit map. Right invariance of
Haar measure and transitivity show that the choice of initial direction does
not affect the result. The dimension bound in `probability` ensures that a
direction exists, including the cases `k = 0` and `k = n`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.Grassmannian

variable {n k : ℕ}

end NKBesicovitch.Grassmannian
