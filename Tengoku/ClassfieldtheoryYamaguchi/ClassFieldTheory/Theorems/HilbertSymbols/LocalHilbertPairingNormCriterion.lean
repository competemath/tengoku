/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Norm-residue criterion for a local Hilbert pairing

The vanishing of a local Hilbert symbol is equivalent to a concrete Kummer
norm condition.  The Kummer algebra is the canonical Mathlib quotient
`K[X] / (X^n - a)`, so the statement does not choose a root in an algebraic
closure.
-/

namespace ClassFieldTheory

universe u

/-- A local Hilbert pairing evaluates to one exactly on Kummer norms.
@isnad1 id=iff.1h5v.s8.f44229c0308c from=translated src=- shape=0f89834d vocab=ac714a09
-/
theorem localHilbertPairing_eq_one_iff_isKummerNorm
    (K : Type u) [Field K] (n : ℕ+)
    (B : HilbertPairing K n)
    (hB : HilbertPairing.IsLocalHilbertPairing B)
    (a b : Kˣ) :
    B.symbol a b = 1 ↔ IsKummerNorm K n a b := by
  exact hB.2.2.2 a b

end ClassFieldTheory
