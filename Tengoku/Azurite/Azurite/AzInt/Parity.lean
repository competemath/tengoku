/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Basic
import Tengoku.Azurite.Azurite.AzNat.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite

/-- Efficient parity test for integers: delegates to absolute value.-/
def AzInt.isEven (z : AzInt) : Bool := z.abs.isEven

/-- Efficient parity test for integers: delegates to absolute value.-/
def AzInt.isOdd (z : AzInt) : Bool := z.abs.isOdd

end Azurite
