/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.AlgebraicPuiseux
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Theorem_2_92

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — `C⟨ε⟩` is an algebraic closure of `C(ε)`

This is the algebraically closed analogue of Corollary 2.98. When `C` is algebraically closed of
characteristic zero, Theorem 2.92 says the Puiseux series `C⟨⟨ε⟩⟩ = PuiseuxSeries C` are
algebraically closed. Hence the field `C⟨ε⟩ = algebraicPuiseux C` of *algebraic* Puiseux series — the
relative algebraic closure of `C(ε) = RatFunc C` inside `C⟨⟨ε⟩⟩` — is an algebraic closure of `C(ε)`:
it is algebraically closed (this file) and, by construction, algebraic over `C(ε)`.

In the case `C = R[i]` for `R` real closed, this matches the field `R⟨ε⟩[i]` obtained from
Corollary 2.98 (`R⟨ε⟩` is real closed) together with Theorem 2.11 (`R⟨ε⟩[i]` is algebraically
closed): `C⟨ε⟩ = R⟨ε⟩[i]`. -/

namespace Azurite.BPR

open Polynomial

end Azurite.BPR
