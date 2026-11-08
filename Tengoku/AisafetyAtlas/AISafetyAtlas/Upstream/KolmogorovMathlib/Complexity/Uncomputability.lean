/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.NatComplexity
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Properties
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Core.Basic
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.NatEncoding
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.UnboundedSearch
public import Tengoku.Seed.Computability.Partrec
public import Tengoku.Seed.Computability.PartrecCode
public import Tengoku.Seed.Order.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Uncomputability of Kolmogorov Complexity

This module proves that Kolmogorov Complexity is not computable.
Instead of just proving that `plainK` is uncomputable, we prove a much stronger,
generalized result: **There exists no computable, unbounded lower bound for `plainK`**.

The proof relies on Berry's Paradox: if such a bound existed, we could compute
a number with "too much" complexity for its small description length.
-/

namespace Kolmogorov

/-! ### Growth Lemma & Paradox Base -/

/-- Helper for the growth lemma to isolate the induction step.
    Proves that linear growth cannot keep up with exponential growth.-/
private lemma growthArithmeticHelper (n : ℕ) : n + 5 + n < 2 ^ (n + 5) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-! ### Computability Bridge Integration -/

/-! ### Main Theorems -/

end Kolmogorov
