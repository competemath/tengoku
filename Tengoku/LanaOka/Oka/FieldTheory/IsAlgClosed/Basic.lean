/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.FieldTheory.Separable
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Over an algebraically closed field, `x ^ n = a` has exactly `n` solutions

Material for `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`; see `README.md` on the mirror tree.
All three imports are already in that file's transitive closure, so upstreaming this costs it
**no** new imports — measured by breadth-first search over `^(public )?import` in
`.lake/packages/mathlib`, against a closure of **1669** Mathlib modules.

**The instrument masks comments before matching, and that is not tidiness.** **Fourteen** files of
Mathlib carry a line that begins `import …` inside a docstring or a comment — 29 such lines in all,
of which **two are a bare `import Mathlib`** (`Mathlib/Tactic/Rify.lean` and
`Mathlib/Analysis/Normed/Algebra/Exponential.lean`), at which point an unmasked breadth-first
search returns the whole library. The one that bites hardest in practice is
`Mathlib/Tactic/FunProp.lean`, whose documentation shows
`import Mathlib.Analysis.Complex.Trigonometric` in an example: `Mathlib.Tactic.FunProp` is in
almost every closure, so an unmasked search silently pulls that module's entire closure — 1238
Mathlib modules — into almost everything.

**How much of that is new depends on the baseline, so the figure is not a property of the edge.**
Against the 1669 above it adds **223**; against
`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`'s closure of 1473 it adds
**271**, which is where this was first noticed. **And they are not analysis modules**: of the 223
here, **8** are under `Mathlib/Analysis/` and the other **215** are the substrate
`Mathlib.Analysis.Complex.Trigonometric` is built on — topology 122, order 34, algebra 29, data
23, and 7 modules of tactic and logic infrastructure. A sentence of the form *"that edge adds N
analysis modules"* is wrong on both counts and this one used to be.

## Why this is not in `Oka/Analysis/Complex/CoveringMap.lean`

That file holds `isClosedMap_npow` and `finite_fiber_npow`, the two other properties of the map
`x ↦ xⁿ` on `{x : 𝕜 // x ≠ 0}` that `Mathlib/Analysis/Complex/CoveringMap.lean` would want, and it
is the obvious place to *read* a fibre count. It is the wrong place to put one, for two reasons and
both are measured rather than argued:

* **The statement is not analytic.** It uses no norm, no topology and no `ProperSpace`; what makes
  the count uniform is algebraic closure. Its two neighbours hold over any `NontriviallyNormedField`
  and this does not — over `ℝ` the fibres of `x ↦ x ^ 2` on the nonzero reals have two points over a
  positive number and none over a negative one — so it is not their generality with one more
  conclusion, it is a different theorem.
* **It would cost that file 228 new Mathlib modules**, against its target's closure of 2071.
  `README.md` records 96 files as the figure that once made an upstreaming judged too expensive, so
  228 is well past what this repository has been willing to pay. Splitting by destination costs
  nothing instead: `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` already has every import this needs.

Mathlib counts the roots of `X ^ n - C a` in several places and never in this form. What it has is
`Polynomial.card_nthRoots`, an *inequality* on a multiset with multiplicity, and — in
`Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`, which nothing in this repository imports, so
the two names are given as prose rather than in backticks — an equality on that multiset in the
`IsPrimitiveRoot` namespace, which needs a primitive root supplied by hand, and its `Finset` form,
which is the case `a = 1`. **None of them is a statement about the cardinality of
`{x // x ^ n = a}`**, which is the shape a consumer counting the points of a fibre needs, and which
is what this file adds.

## The proof, and that it is Mathlib's own idiom

`Polynomial.separable_X_pow_sub_C` plus `Polynomial.card_rootSet_eq_natDegree` at
`IsAlgClosed.splits_domain`. That exact combination already appears in the target file, in the
proof that an algebraically closed field is infinite
(`Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, the `Infinite` instance), at `a = 1`; the only
work here is carrying it to a general `a` and turning the `Polynomial.rootSet` into the subtype.

**No primitive root of unity is constructed and none is needed.** Separability of `X ^ n - C a`
is what makes the roots distinct, and separability is exactly `(n : F) ≠ 0` together with
`a ≠ 0` — which is why the hypotheses are those two and not a characteristic assumption.

## Main results

- `IsAlgClosed.card_setOf_pow_eq`
-/

open Polynomial

namespace IsAlgClosed

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- **Over an algebraically closed field, `x ^ n = a` has exactly `n` solutions**, provided
`(n : F) ≠ 0` and `a ≠ 0`.

Both hypotheses are needed and neither can be weakened to the other's absence. If `a = 0` the
only solution is `x = 0`, whatever `n` is. If `(n : F) = 0` — that is, if the characteristic
divides `n` — the polynomial `X ^ n - C a` is a `p`-th power and its roots collapse; over
`ZMod 2` extended to an algebraic closure, `x ^ 2 = a` has one solution and not two.

Stated as `Nat.card` of a subtype rather than as the cardinality of `Polynomial.nthRootsFinset`,
because the consumer is counting the points of a fibre and `Polynomial.nthRootsFinset_toSet`
already identifies the two sets. Mathlib has the case `a = 1` in the `IsPrimitiveRoot` namespace
(see the module docstring on why that name is not in backticks), by a different route: that one
goes through a primitive root and this one does not. -/
theorem card_setOf_pow_eq {n : ℕ} {a : F} (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
    Nat.card {x : F // x ^ n = a} = n := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hne : (X ^ n - C a : F[X]) ≠ 0 := X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn0) a
  have hcard := card_rootSet_eq_natDegree (K := F)
    (separable_X_pow_sub_C a hn ha) (IsAlgClosed.splits_domain (X ^ n - C a))
  rw [natDegree_X_pow_sub_C] at hcard
  have hset : (X ^ n - C a).rootSet F = {x : F | x ^ n = a} := by
    ext x
    simp [mem_rootSet, hne, sub_eq_zero]
  rw [← Nat.card_eq_fintype_card, hset] at hcard
  exact hcard

end IsAlgClosed
