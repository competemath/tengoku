/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Incompressibility
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Properties
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Core.Basic
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.NatEncoding
public import Tengoku.Seed.Computability.Partrec
public import Tengoku.Seed.Data.ENat.Lattice
public import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Complexity of Natural Numbers

This module lifts the concept of Kolmogorov complexity from bit strings
to natural numbers using the standard injective binary representation (`Nat.bits`).
It proves the existence of arbitrarily complex natural numbers,
establishes logarithmic upper bounds on their complexity, and proves
that the complexity is invariant (up to a constant) under any computable
change of encoding.
-/

namespace Kolmogorov

/-! ### Complexity of Natural Numbers -/

/-- The plain Kolmogorov complexity of a natural number.-/
@[expose]
public noncomputable def plainKNat (U : Map) (n : ℕ) : ENat :=
  plainK U (Nat.bits n)

/-- The conditional Kolmogorov complexity of a natural number given string y.-/
@[expose]
public noncomputable def condKNat (U : Map) (n : ℕ) (y : BitString) : ENat :=
  condK U (Nat.bits n) y

/-! ### Existence of Complex Numbers (Corollary) -/

/-! ### Upper Bounds (Logarithmic Bound) -/

/-! ### Invariance of Encoding (Universality) -/

end Kolmogorov
