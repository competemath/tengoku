/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.Algebra.Field.Subfield.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport of the automorphism group along an equality of base subfields

For a field `K` and two subfields `S T : Subfield K` with `S = T`, the two automorphism groups
`K ≃ₐ[↥S] K` and `K ≃ₐ[↥T] K` are isomorphic, by the identity on underlying functions.

⚠️ **Nothing about elliptic curves enters this file.**  It is stated for an arbitrary field and an
arbitrary pair of equal subfields, and it imports nothing from this development — the
`EllipticCurves`-import closure of this module is empty.

## Why this file exists

An Artin-sandwich argument produces a fixed field as `FixedPoints.subfield G K`, and
`FixedPoints.toAlgAutMulEquiv` identifies `G` with `K ≃ₐ[↥(FixedPoints.subfield G K)] K` — the
automorphism group over *that* presentation of the base.  What a consumer holds is a theorem saying
the fixed field **is** some subfield it cares about, and the two automorphism groups are then
different types with the same elements.  This file is the one-declaration bridge, and it is the only
brick its two consumers — `EllipticCurves.FunctionField.MulByNGaloisGroup` for `[n]∗F(W)` and
`EllipticCurves.FunctionField.NegYGaloisGroup` for `F(x)` — had to build.

## Import weight, and ⚠️ the `^import` regex that silently under-reads it

Measured at `320f413` with a header-only walker (block comments skipped nesting-aware, so the
`import Mathlib` inside `Mathlib/Tactic/Rify.lean`'s docstring is not read as an edge), over this
project plus all nine `.lake/packages` — 9837 `.lean` **files**, each package's own nested
`.lake/` build tree excluded.  Files, not modules: mathlib's and proofwidgets' `lakefile.lean`
collide, so the walker indexes 9836 distinct names.  ⚠️ **A name that resolves to no file in those
trees is not an edge** — `Lean.*`, `Init.*` and `Std.*` live in the toolchain, not in the nine
packages, and counting them puts this file's total at 1146 rather than 968.  That is an 18% error
with nothing absurd about it, which is this section's whole subject.

| module | `EllipticCurves` closure | total closure | total under `^import\s` alone |
| --- | --- | --- | --- |
| `Galois.SubfieldAut` (this file) | **0** | **968** | 3 |
| `FunctionField.NegYGaloisGroup` | 22 | 2668 | 47 |
| `FunctionField.MulByNGaloisGroup` | 74 | 2802 | 115 |

⚠️ **The two closure columns count the module itself differently**, and assuming one convention for
both is how a re-run comes out one high on three cells.  The total counts it; the `EllipticCurves`
column does not — that column is the sense in which this file's own `EllipticCurves`-import closure
is empty, and in which `#1266` cut `NegYGaloisGroup` from 71 to 19.

⚠️ **The totals are falsifiable, and this is the check.**  `lake build` on the three modules reports
**983**, **2683** and **2817** jobs — the walker's total plus a constant **15** on every row, across
closures spanning 968 to 2802.  Three numbers out of a hand-rolled walker are otherwise
unfalsifiable; a constant offset against lake's own module graph is not.

The relocation that created this file is what the first column is for: on **one tree**, across the
single commit `008fea7`, `NegYGaloisGroup`'s project closure fell **71 → 19** — it is 22 today, the
tree having grown from 359 modules to 387 — while `MulByNGaloisGroup` rose 70 → 71, the one new
module being this one.  ⚠️ That saving is **52** modules as measured here; `#1259` and `#1267`
record it as 53, and the difference is the self-counting convention: consistent counting gives 52
either way (`71 → 19` excluding the module, `72 → 20` including it), while `72 − 19` — one
convention on each side — gives 53.

⚠️ **The third column is not a typo, and it is the reason to write this section down.**  Mathlib at
this pin uses the Lean module system, so `Mathlib/Algebra/Algebra/Equiv.lean` — this file's own
first import — opens `module` / `public import Mathlib.Algebra.Algebra.Hom`, and a script matching
`^import\s+(\S+)` reads it as importing **nothing**.  The pattern that works is

```python
re.compile(r'^(?:public |private |meta |protected )*import\s+(?:all\s+)?(\S+)')
```

⚠️ **That pattern is necessary and not sufficient: where the header ends is a second, independent
decision, and it moves the number.**  The third column is what a walker gets by reading the whole
header and ignoring lines its pattern cannot parse — the experiment that changes only the capture
pattern.  A walker that instead *stops* at the first unparsable line halts on the opening
`public import` and reports `3 / 44 / 112`; the three edges it drops are ordinary non-`public`
imports placed after the public block, as `Mathlib/RingTheory/Algebraic/Integral.lean` places
`import Mathlib.RingTheory.Polynomial.Subring`.

⚠️ **Why the bug does not announce itself.**  Nothing in this development writes `public import`, so
the *project* column is exact under either pattern and every project-side sanity check passes.  Only
the total is wrong, and it is wrong by a factor of 24 (`2802 / 115`) to 323 (`968 / 3`) — a number
small enough to look like a plausible import count rather than an absurd one.  Census, `.lean` files
/ with a `^public import ` line / with a plain `^import ` line.  ⚠️ **The rows are not scoped
alike**: mathlib's is `Mathlib/` only, every other package's is the whole package tree minus its
nested `.lake/`.  Scoping the others the way mathlib's is scoped — to `batteries/Batteries`,
`aesop/Aesop`, … — reads batteries as 187 files rather than 254, and shifts every row but mathlib's
and the project's.

| tree | files | `^public import ` | `^import ` |
| --- | --- | --- | --- |
| `EllipticCurves/` | 386 | **0** | **386** |
| `.lake/packages/mathlib/Mathlib` | 8264 | **8246** | 381 |
| `.lake/packages/batteries` | 254 | 127 | 82 |
| `.lake/packages/aesop` | 250 | 125 | 161 |
| `.lake/packages/proofwidgets` | 46 | 25 | 5 |
| `.lake/packages/importGraph` | 37 | 18 | 22 |
| `.lake/packages/Qq` | 28 | 12 | 15 |
| `.lake/packages/plausible` | 28 | 6 | 17 |
| `.lake/packages/Cli` | 5 | 3 | 2 |
| `.lake/packages/LeanSearchClient` | 8 | 0 | 0 |

⚠️ **The project row is the control**: if it does not come out `0` public and one plain
`import` line per file, the census is reading the wrong tree.  (Its *file count* is not the
control — it was 360 when this was first measured and is 386 now.)

⚠️ **The module system is a toolchain convention, not a Mathlib one.**  **Eight** of the nine
vendored packages use `public import` — every one but `LeanSearchClient`, which has no `import`
line at all.  Scoping a verification `grep` to `Mathlib/` bounds the blind spot over Mathlib
alone, while every closure above walks all nine.  The same holds for `import all M`, which
suppresses nothing but must still be matched: `Mathlib/` writes it 23 times in 21 files,
`MathlibTest/` in 10 more, and **Batteries in 13** — of the **10** `import all` modules inside
this file's own closure, **5 are Batteries'**.

⚠️ **Do not take a matching total as evidence your pattern is right.**  At this SHA, dropping the
`(?:all\s+)?` alternative changes **none** of the three totals, because every `import all` target is
reachable by another path — so that alternative is a correctness requirement whose omission is
invisible in exactly the way `public import`'s is not.

## Mathlib has no name for this

⚠️ Re-grepped at Lean `v4.32.0` / Mathlib `v4.32.0` before this file was cut, and the position is
unchanged from when the declaration was first written:

* `AlgEquiv.autCongr` (`Mathlib/Algebra/Algebra/Equiv.lean`) moves the **top** algebra over a fixed
  base — `(A₁ ≃ₐ[R] A₂) → ((A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂))` — and is not this;
* `IntermediateField.equivOfEq` (`Mathlib/FieldTheory/IntermediateField/Basic.lean`) is an
  `AlgEquiv` between the two intermediate fields **themselves**, not between their automorphism
  groups;
* `autCongr` is *declared* in exactly one place in Mathlib — the file above.  The three other
  Mathlib files that mention it (`FieldTheory/AbelRuffini.lean`, `FieldTheory/KummerExtension.lean`,
  `NumberTheory/Cyclotomic/Gal.lean`) are consumers of that one, not a second, base-changing
  version.

So `Subfield.autMulEquivOfEq` is an upstream candidate.  ⚠️ It is a candidate and not a plan: no
Mathlib pull request exists, and nothing in this development is waiting on one.

## ⚠️ The imports are minimal, and `Subfield.Basic` cannot be weakened to `Subfield.Defs`

Both imports were tested by deletion and both are needed.  `Mathlib.Algebra.Field.Subfield.Defs`
does make this file *elaborate* — but it makes it elaborate against a **different** `Algebra ↥S K`
instance.  Measured with `set_option pp.explicit true in #synth Algebra (↥S) K` under each import
set:

* with `Mathlib.Algebra.Field.Subfield.Basic` — `Subfield.toAlgebra`;
* with `Mathlib.Algebra.Field.Subfield.Defs` — `Algebra.ofSubsemiring …`, found through
  `SubsemiringClass`.

`Subfield.toAlgebra` (`Mathlib/Algebra/Field/Subfield/Basic.lean`) is the instance every consumer of
this file resolves, so weakening the import would put a different instance into the *statement* of
`autMulEquivOfEq` and leave consumers to unfold the difference.  ⚠️ **The narrower import is not the
better one here**; do not "optimise" it without re-running that `#synth`.

## Main definitions

Every public declaration of this file is listed, here and under `## Main statements`.  Everything is
in namespace `Subfield`.

* `Subfield.autMulEquivOfEq` — transport of `Aut K` along an equality of base subfields.

## Main statements

* `Subfield.autMulEquivOfEq_apply` and `Subfield.autMulEquivOfEq_symm_apply` — the transport is the
  identity on underlying functions, by `rfl` in both directions.

## What is *not* here

* **No `IntermediateField` twin.**  A consumer whose equality is an `IntermediateField` equality
  drops it to the `Subfield` level first — `SetLike.ext` off the equality it already has — and then
  applies these names.  `EllipticCurves.FunctionField.NegYGaloisGroup` is the worked example, in
  `fixedPoints_subfield_eq_ratFuncRange`; the `≃ₐ` types over the two carriers are definitionally
  equal, which that file commits as an `example`, so a second name here would be noise.
* **Nothing about fixed points.**  `FixedPoints.toAlgAutMulEquiv` is Mathlib's and is what this
  transports *against*; it is not restated, and this file does not import it.
* **No `Normal`, no `IsGalois`, no degree.**  An equality of base subfields carries all three across
  on its own, and no consumer needs a lemma here to say so.
-/

namespace Subfield

variable {K : Type*} [Field K] {S T : Subfield K}

/-- **Equal base subfields give isomorphic automorphism groups**, by the identity on underlying
functions.

An `S`-algebra automorphism of `K` is a ring automorphism that fixes `S` pointwise, and `S = T` says
the two subsets are the same, so nothing is transported except the proof obligation.  The
`MulEquiv` is therefore built out of `AlgEquiv.ofRingEquiv` in both directions and all three
coherence fields are `rfl`. -/
def autMulEquivOfEq (hST : S = T) : (K ≃ₐ[↥S] K) ≃* (K ≃ₐ[↥T] K) where
  toFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.ge r.2⟩
  invFun e := AlgEquiv.ofRingEquiv (f := (e : K ≃+* K)) fun r => e.commutes ⟨r, hST.le r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma autMulEquivOfEq_apply (hST : S = T) (e : K ≃ₐ[↥S] K) (x : K) :
    autMulEquivOfEq hST e x = e x := rfl

@[simp] lemma autMulEquivOfEq_symm_apply (hST : S = T) (e : K ≃ₐ[↥T] K) (x : K) :
    (autMulEquivOfEq hST).symm e x = e x := rfl

end Subfield
