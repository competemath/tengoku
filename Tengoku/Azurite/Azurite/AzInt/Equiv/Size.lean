/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Size
import Tengoku.Azurite.Azurite.AzInt.Equiv.Conversion
import Tengoku.Azurite.Azurite.AzNat.Equiv.Size
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite.AzInt

/--
@isnad1 id=eq.0h1v.s3.dc3baa113036 from=translated src=- shape=63f53019 vocab=04abc806
-/
theorem size_toInt (z : AzInt) : z.toInt.natAbs.size = z.size := by
  unfold AzInt.size
  rw [← toNat_natAbs z, AzNat.size_toNat]
  rfl

/--
@isnad1 id=eq.0h1v.s3.72c6e47a6127 from=translated src=- shape=69b989be vocab=e0bac09d
-/
theorem size_eq_int_size (z : AzInt) : z.size = BPR.Int.size z.toInt := by
  unfold BPR.Int.size
  exact size_toInt z |>.symm

/--
@isnad1 id=eq.0h1v.s3.7682f465a250 from=translated src=- shape=7367b1cd vocab=82e94c96
-/
theorem size_ofInt (i : Int) : (ofInt i).size = i.natAbs.size := by
  rw [← size_toInt, toInt_ofInt]

end Azurite.AzInt
