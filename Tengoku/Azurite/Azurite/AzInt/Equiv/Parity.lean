/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Parity
import Tengoku.Azurite.Azurite.AzInt.Equiv.Basic
import Tengoku.Azurite.Azurite.AzInt.Equiv.Conversion
import Tengoku.Azurite.Azurite.AzNat.Equiv.Parity
import Tengoku.Seed.Algebra.Ring.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite.AzInt

private lemma even_int_iff_even_natAbs (z : Int) : Even z ↔ Even z.natAbs := by
  rw [Nat.even_iff, Int.even_iff]
  constructor <;> intro h <;> omega

/--
@isnad1 id=iff.0h1v.s3.e8d882a0e5d9 from=translated src=- shape=70149ad5 vocab=12829c4c
-/
theorem isEven_iff (z : AzInt) : z.isEven = true ↔ Even z.toInt := by
  unfold AzInt.isEven
  rw [even_int_iff_even_natAbs, ← toNat_natAbs]
  exact AzNat.isEven_iff z.abs

private lemma odd_int_iff_odd_natAbs (z : Int) : Odd z ↔ Odd z.natAbs := by
  rw [Nat.odd_iff, Int.odd_iff]
  constructor <;> intro h <;> omega

/--
@isnad1 id=iff.0h1v.s3.7273bbf5429d from=translated src=- shape=70149ad5 vocab=8f6adc6c
-/
theorem isOdd_iff (z : AzInt) : z.isOdd = true ↔ Odd z.toInt := by
  unfold AzInt.isOdd
  rw [odd_int_iff_odd_natAbs, ← toNat_natAbs]
  exact AzNat.isOdd_iff z.abs

/--
@isnad1 id=iff.0h1v.s3.4ff52393b1f0 from=translated src=- shape=58e99329 vocab=baf225ba
-/
theorem isEven_ofInt (i : Int) : (ofInt i).isEven = true ↔ Even i := by
  rw [isEven_iff, toInt_ofInt]

/--
@isnad1 id=iff.0h1v.s3.bcf1211ee83b from=translated src=- shape=58e99329 vocab=d75645ba
-/
theorem isOdd_ofInt (i : Int) : (ofInt i).isOdd = true ↔ Odd i := by
  rw [isOdd_iff, toInt_ofInt]

end Azurite.AzInt
