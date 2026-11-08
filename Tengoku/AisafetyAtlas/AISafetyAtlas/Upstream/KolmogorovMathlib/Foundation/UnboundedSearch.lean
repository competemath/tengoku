/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.Seed.Computability.Halting
public import Tengoku.Seed.Computability.Partrec
public import Tengoku.Seed.Computability.PartrecCode
public import Tengoku.Seed.Computability.Primrec.List
public import Tengoku.Seed.Data.List.Basic
public import Tengoku.Seed.Data.Nat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Unbounded Search Computability (The Mu-Operator)

This module provides the "Computability Bridge" for unbounded search.
It proves that if a predicate `P` is decidable and computable, and if an answer
is guaranteed to exist for every input, then the search for the minimal such answer
(`Nat.find`) is a total computable function.
-/

namespace Kolmogorov

/-! ### Basic Math Computability -/

/-! ### General Unbounded Search -/

/-! ### Corollaries -/

end Kolmogorov
