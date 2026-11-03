/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Basic
import Tengoku.Azurite.Azurite.AzNat.Pow2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite

/-- Construct the AzInt equal to `2 ^ k`.-/
def AzInt.pow2 (k : Nat) : AzInt where
  sign := true
  abs := AzNat.pow2 k
  zero_sign := by
    intro h
    have := (AzNat.pow2 k).last_ne_zero
    rw [h] at this

/-- Test whether an AzInt is a positive power of 2 (i.e. `2 ^ k` for some `k : Nat`).-/
def AzInt.isPowerOfTwo (z : AzInt) : Bool :=
  z.sign && z.abs.isPowerOfTwo

end Azurite
