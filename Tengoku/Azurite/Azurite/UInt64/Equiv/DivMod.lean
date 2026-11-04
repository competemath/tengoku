/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.UInt64.DivMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace UInt64

/-- The first component of `divMod x y` is `x / y` (Nat-level).
@isnad1 id=eq.0h2v.s4.75a81e0f6878 from=translated src=- shape=f176fa77 vocab=1016f7b2
-/
theorem toNat_divMod_fst (x y : UInt64) :
    (divMod x y).1.toNat = x.toNat / y.toNat :=
  _root_.UInt64.toNat_div x y

/-- The second component of `divMod x y` is `x % y` (Nat-level).
@isnad1 id=eq.0h2v.s4.cf03c1a15732 from=translated src=- shape=f176fa77 vocab=0e1876ff
-/
theorem toNat_divMod_snd (x y : UInt64) :
    (divMod x y).2.toNat = x.toNat % y.toNat :=
  _root_.UInt64.toNat_mod x y

end UInt64
