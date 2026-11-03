/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.LowMask
import Tengoku.Azurite.Azurite.AzInt.Equiv.Basic
import Tengoku.Azurite.Azurite.AzNat.Equiv.LowMask

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite.AzInt

/--
@isnad1 id=eq.0h1v.s5.e72938a21ecb from=translated src=- shape=ee4ab1ce vocab=cf62b7d8
-/
theorem toInt_lowMask (k : Nat) : (AzInt.lowMask k).toInt = 2 ^ k - 1 := by
  unfold AzInt.lowMask toInt
  simp [AzNat.toNat_lowMask]

/--
@isnad1 id=eq.0h1v.s5.44c7cfbc28c1 from=translated src=- shape=33278cd2 vocab=861d0ec4
-/
theorem lowMask_eq_ofInt (k : Nat) : AzInt.lowMask k = ofInt (2 ^ k - 1) := by
  have h : (AzInt.lowMask k).toInt = (ofInt (2 ^ k - 1)).toInt := by
    rw [toInt_lowMask, toInt_ofInt]
  exact ofInt_toInt (AzInt.lowMask k) ▸ ofInt_toInt (ofInt (2 ^ k - 1)) ▸ congrArg ofInt h

end Azurite.AzInt
