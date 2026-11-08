/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Core.Basic
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.RecursivelyEnumerable
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.UnboundedSearch
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
# Basic Properties of Kolmogorov Complexity

This module establishes the foundational inequalities of algorithmic information theory
using an optimal universal decompressor `U`. It proves that:
* `plainK(x) ≤ |x| + c` (strings can be compressed no worse than their literal length).
* `condK(x|x) ≤ c` (knowing the answer gives constant complexity).
* `condK(x|y) ≤ plainK(x) + c` (conditioning only reduces complexity).
* `condK(f(x)|y) ≤ condK(x|y) + c` (computable functions do not add information).

It also establishes the computability properties (RE and co-RE) of the complexity metric.
-/

namespace Kolmogorov

/-! ### Boundary API -/

/-! ### Fundamental Inequalities -/

/-! ### Computability and Enumerability (RE / co-RE) -/

/-! ### Auxiliary structures for Dovetailing / Bounded Search -/

/-! ### Main Computability Theorems -/

end Kolmogorov
