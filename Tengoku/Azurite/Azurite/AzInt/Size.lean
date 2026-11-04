/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Basic
import Tengoku.Azurite.Azurite.AzNat.Size

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite

/-- The number of bits required to represent the integer's absolute value in binary.
Equivalent to `Nat.size` applied to the natural absolute value.-/
def AzInt.size (z : AzInt) : Nat := z.abs.size

end Azurite
