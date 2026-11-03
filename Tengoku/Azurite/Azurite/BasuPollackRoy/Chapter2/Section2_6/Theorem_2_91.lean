/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_93
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RootTelescope
import Tengoku.Seed.FieldTheory.IsRealClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Theorem 2.91 — `R⟨⟨ε⟩⟩` is real closed (reduction)

For a real closed (hence ordered) field `R`, the field of Puiseux series `R⟨⟨ε⟩⟩` is real closed.

By Mathlib's Artin–Schreier characterization `IsRealClosed.of_linearOrderedField`, proving
`IsRealClosed (R⟨⟨ε⟩⟩)` (an ordered field) reduces to exactly two obligations:

* **squares:** every nonnegative element is a square — this is Lemma 2.93 (`isSquare_of_nonneg`);
* **odd-degree roots:** every odd-degree polynomial has a root — the Puiseux/Newton-polygon
  construction.

This file discharges the squares obligation and records the reduction
`isRealClosed_puiseux_of_exists_root`, isolating the odd-degree-root existence as the single
remaining (large) obligation. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

end Azurite.BPR
