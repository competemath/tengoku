/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Pairings on power classes
-/

namespace ClassFieldTheory

universe u

/-- Multiplicative pairings on `n`-th power classes with values in the
`n`-th roots of unity.-/
abbrev HilbertPairing (K : Type u) [Field K] (n : ℕ+) :=
  PowerClassGroup K n →*
    (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K)

end ClassFieldTheory
