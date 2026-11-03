/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Basic
import Tengoku.Azurite.Azurite.AzNat.LowMask

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite

/-- Construct the AzInt with the lowest `k` bits set, equal to `2 ^ k - 1`.-/
def AzInt.lowMask (k : Nat) : AzInt where
  sign := true
  abs := AzNat.lowMask k
  zero_sign := by
    intro h
    have := (AzNat.lowMask k).last_ne_zero
    rw [h] at this

end Azurite
