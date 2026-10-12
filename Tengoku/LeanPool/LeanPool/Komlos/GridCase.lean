/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Tengoku.LeanPool.LeanPool.Komlos.NearInvariant
public import Tengoku.LeanPool.LeanPool.Komlos.SignedSums
public import Tengoku

/-!
# The Komlós bound on a grid

Adapted for Lean Pool by changing module paths and selecting explicit imports.

For vectors on `N⁻¹ • ℤ ^ d`, the distribution from Lemma 1.5 satisfies the hypotheses of
Lemma 1.4 after scaling the vectors by `1 / 6`. The resulting signed sum has supremum norm
at most `36`.
-/

@[expose] public section

namespace Komlos

open Finset Matrix

end Komlos
