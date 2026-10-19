/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.AlgebraicGeometry.OpenImmersion

/-!
# Sections over the range of an open immersion of schemes, in `basicOpen` form

Material for `Mathlib/AlgebraicGeometry/OpenImmersion.lean`; see `README.md` on the mirror tree.
Upstreaming it adds nothing: that file's transitive closure is **2039** Mathlib modules, the
import above is the target itself, and the cost is **0**, measured with

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
`python3 scripts/import_cost.py Oka/AlgebraicGeometry/OpenImmersion.lean`. There is no competing
destination to weigh against it.

`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop` there is `Γ(X, ⊤) ≅ Γ(Y, f.opensRange)` for an open
immersion `f : X ⟶ Y`. **Everything this file adds is about `basicOpen`**, because that is what a
caller who has reached for the isomorphism wants next: the distinguished open of a section over
`f.opensRange` is the image of a distinguished open of `X`. The `Spec` isomorphism below is the
same statement's input in the form a caller with an affine open cover is in, and it is one
`AlgebraicGeometry.Scheme.ΓSpecIso` away from Mathlib's.

## The isomorphism itself is Mathlib's, and this file's first version redefined it

**`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop` is 570 lines below the
`AlgebraicGeometry.Scheme.Hom.appIso` this file's first version cited, in the file it names as its
upstream target** — line 225 against line 795 of
`Mathlib/AlgebraicGeometry/OpenImmersion.lean`. That version declared
*Scheme.Hom.opensRangeIso* (not backticked, because it names nothing in this tree) as
`Γ(Y, f.opensRange)` ≅ `Γ(X, ⊤)`, out of the same two components routed the same way and pointing
the other way — so `(IsOpenImmersion.ΓIsoTop f).symm` on the nose. Re-run here rather than taken
from the review that found it: restoring the old definition in a scratch file and elaborating
`ext : 1; simp [IsOpenImmersion.ΓIsoTop]` against it is `lake env lean`, **exit 0**. It was
caught in review (lana-agents/oka#374) and removed.

A mirror-tree file cannot hold a declaration that is already in its target file: `README.md` makes
the mirror path *"a claim about where the results would go upstream"*, so a duplicate there is a
wrong claim about the destination and not only a redundant name.

**The check that would have found it takes one command and it is not the import-cost check.**

```
grep -rn "opensRange" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/ --include=*.lean | grep "≅"
```

It returns **six** lines and the two that matter are the first two, both in the target file
itself: `Mathlib/AlgebraicGeometry/OpenImmersion.lean:770`, which is
`AlgebraicGeometry.IsOpenImmersion.ΓIso`, and `:796`, which is the statement. The other four are
`Restrict.lean:419` (`X ≅ f.opensRange`, a scheme and not a ring), `Restrict.lean:695` and
`Pullbacks.lean:659` (isomorphisms of `CategoryTheory.Arrow`) and
`Morphisms/RingHomProperties.lean:606` (a `let` inside a proof). **Reading the hits is the step,
not counting them** — a first draft of this paragraph said *"three hits"*, which is the same
species of defect as the one the paragraph is about.

**For a mirror-tree file the search is for the *statement*, and it has to run before the file is
written**; the import-cost measurement is the second test and it passed at 0 while the first had
never been run. `README.md`'s mirror-tree section is where this belongs if it is ever written down
as a rule rather than as this paragraph.

## Why `basicOpen` survives the transport, and it is Mathlib's design decision and not ours

`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop` spends the equality
`AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange` as `Y.presheaf.mapIso` rather than as an
`eqToIso` between the two rings, and **that choice is exactly what makes the two theorems below
four rewrites each.** `AlgebraicGeometry.Scheme.basicOpen_res_eq` — *`basicOpen` is unchanged by
restriction along an isomorphism of opens* — is stated for `X.presheaf.map i` with `[IsIso i]`, and
an `eqToHom` between two ring objects is not of that shape. Measured here, on this file's first
version, which had reconstructed Mathlib's definition down to this decision before knowing it was
Mathlib's: with the `eqToIso` spelling the first theorem below leaves a heterogeneous goal
`(f.appIso ⊤).inv r ≍ …` that `congr` produces and nothing discharges. The two spellings are
propositionally equal and the choice is entirely about which lemma applies to the result.

## Naming Mathlib's definition in a `rw` plants an equation lemma into Mathlib's namespace

`rw [ΓIsoTop, …]` is the obvious spelling of the first proof below and it is the wrong one:
naming a `def` as a rewrite rule asks Lean to generate its equation lemma, and `ΓIsoTop` is
**not this repository's declaration**. Measured — `scripts/DumpOkaDecls.lean` on the draft that
did it reports `AlgebraicGeometry.IsOpenImmersion.ΓIsoTop.eq_1` as declared by
`Oka.AlgebraicGeometry.OpenImmersion`, so this module was adding a lemma to a Mathlib definition
it only imports. `Oka/Analytification/RefineDatumRange.lean` and
`Oka/Analytification/RefineDatumCocycle.lean` record the same hazard by two other routes,
`simp only` and `CategoryTheory.reassoc_of%`; **this is the third route and the cheapest to walk
into, because the rewrite is the one a reader would write first.**

What replaces it is `have h : (ΓIsoTop f).hom = … := rfl` and a rewrite by `h`. A `rfl` proof goes
through definitional unfolding, which generates nothing, and the equation is then local to the
proof. The same substitution is made below for `specΓIsoTop`, which is this file's own definition
and where the cost is only a stray row in the dump; with both, `Δdump` is **+3** for the three
declarations here.

**At `v4.32.0` — the revision `lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` — Mathlib has no lemma about the `hom` or the `inv` of
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`, under that name or any other**:
`grep -rn "ΓIsoTop" Mathlib/` returns **four** occurrences in **two** files — the `def` at
`Mathlib/AlgebraicGeometry/OpenImmersion.lean:795`, and three uses inside proofs at
`Mathlib/AlgebraicGeometry/Noetherian.lean:140`, `:148` and `:172` — so the only occurrence in a
*statement* is the definition itself.

**Here the `grep` decides the claim rather than narrowing it.** A lemma about `(ΓIsoTop f).hom`
or `(ΓIsoTop f).inv` has to write the token `ΓIsoTop` in its own statement, whatever namespace is
open, and it cannot be stated about `ΓIso` instead: `ΓIsoTop` is a `def` in its own right and
**not** `ΓIso f ⊤`, whose type is `Γ(X, f ⁻¹ᵁ ⊤) ≅ Γ(Y, f.opensRange ⊓ ⊤)` and not
`Γ(X, ⊤) ≅ Γ(Y, f.opensRange)` — so a rewrite by a `ΓIso` lemma does not fire on a goal carrying the
token. A `variable` binder introducing `f` and its instance leaves the projection still to be
written, so nothing is inherited from a binder the scan does not read. And the one thing a scan of
source cannot see — an equation lemma generated on demand for the `def` — unfolds the whole
definition rather than projecting a field, which is the rewrite the paragraph above is about
avoiding. **The environment agrees and is deliberately the weaker of the two routes**: of the names
`scripts/DumpEnvNames.lean` dumps at the commit this paragraph is written at, exactly **three**
contain `ΓIsoTop` — Mathlib's `def` and the two this file declares,
`AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` and
`AlgebraicGeometry.IsOpenImmersion.image_basicOpen_ΓIsoTop` — and none of the **9023** generated
`.eq_1` names among them is one. That route cannot be the primary one: the dump is the environment
of `Oka`, which imports some of Mathlib and not all of it, so an absence in it is an absence from
this build's imports and not from Mathlib.

**The control is a positive one, because a scan returning nothing is weaker than one that returns
something next door.** At the same rev, `grep -rn "ΓIsoTop_\|ΓIso_hom\|ΓIso_inv" Mathlib/`
returns **six** lines in **two** files — the three declarations `ΓIso_inv`, `map_ΓIso_inv` and
`app_ΓIso_hom` at `Mathlib/AlgebraicGeometry/OpenImmersion.lean:775`, `:782` and `:787`, and
three use sites at `:789`, `:790` and `Mathlib/AlgebraicGeometry/Cover/Open.lean:240` — and
nothing at `Top`. So the neighbouring `AlgebraicGeometry.IsOpenImmersion.ΓIso` has the projection
lemmas this one lacks.

**That clause read *Mathlib has no `ΓIsoTop_hom` or `ΓIsoTop_inv`* until 2026-09-21**, with the
`grep` above restricted to `Mathlib/AlgebraicGeometry/` as its instrument and no version beside
it; `git show d4c49af:Oka/AlgebraicGeometry/OpenImmersion.lean` carries the retired wording at
`:92–95`, wrapped after *neighbouring*, after *with* and after the backticked command.
**The claim is unchanged and only its warrant is**, which is why the retired wording is kept here
rather than struck: that scan is keyed on **names**, and a lemma stating what `(ΓIsoTop f).hom` is
need not be called `ΓIsoTop_hom`, so as published it narrowed where the token scan above decides.
Widening its directory to all of `Mathlib/` returns the same six lines, so the restriction cost
nothing and is not what was wrong with it. Taxis #2127 is the sweep.

**Supplying the missing lemma here — a `ΓIsoTop_hom` of this file's own — is a candidate and is
deliberately not taken**: it would be a fourth declaration whose only consumer is one `have`, and
the branch this file arrived on was rejected for adding a declaration Mathlib already had. A
later caller that needs the unfolding more than once should add it.

## Main definitions

- `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop`: **for an open immersion `f : Spec R ⟶ Y`,
  sections of `𝒪_Y` over `f.opensRange` are `R` itself**, which is the form a caller with an
  affine open cover is in.

## Main results

- `AlgebraicGeometry.IsOpenImmersion.image_basicOpen_ΓIsoTop`: the image of a distinguished open
  of `X` is the distinguished open of the corresponding section over `f.opensRange`.
- `AlgebraicGeometry.IsOpenImmersion.image_primeSpectrum_basicOpen`: the image of `D(a)` for
  `a : R` is the distinguished open of the corresponding section over `f.opensRange`.

## What is not here

* **No isomorphism between global sections and sections over the range.** That is
  `AlgebraicGeometry.IsOpenImmersion.ΓIsoTop` and it is Mathlib's; the section above says what
  happened to the copy this file used to carry.
* **Nothing along `AlgebraicGeometry.IsAffineOpen.fromSpec`.**
  `AlgebraicGeometry.IsAffineOpen.fromSpec_image_basicOpen` is Mathlib's nearest statement to the
  second theorem below — `hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f` for a section
  `f` over an affine open — and it is a different statement: its morphism is the canonical one
  attached to an affine open and its element is a section of `𝒪_X`, where the one below takes an
  arbitrary open immersion out of a spectrum and an element of the ring. Deducing either from the
  other needs the identification of `R` with `Γ(Y, f.opensRange)`, which is the definition below;
  nothing here does it and nothing here needs it.
* **No naturality and no uniqueness.** Neither isomorphism here is related to a morphism of the
  data it is built from.
-/

open CategoryTheory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry

namespace IsOpenImmersion

section

variable {X Y : Scheme.{u}} (f : X.Hom Y) [IsOpenImmersion f]

/-- **The image of a distinguished open of `X` is the distinguished open of the corresponding
section over `f.opensRange`.**

`AlgebraicGeometry.Scheme.image_basicOpen` states this at `(f.appIso ⊤).inv r`, a section over
`f ''ᵁ ⊤`; the content here is only that transporting it to `f.opensRange` changes nothing, which
is `AlgebraicGeometry.Scheme.basicOpen_res_eq` at the isomorphism of opens inside
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`'s definition — see this file's header for why that
lemma is reachable at all. -/
theorem image_basicOpen_ΓIsoTop (r : Γ(X, ⊤)) :
    f ''ᵁ X.basicOpen r = Y.basicOpen ((ΓIsoTop f).hom r) := by
  have h : (ΓIsoTop f).hom = ((f.appIso ⊤).symm ≪≫
      Y.presheaf.mapIso (eqToIso f.image_top_eq_opensRange.symm).op).hom := rfl
  rw [Scheme.image_basicOpen, h, Iso.trans_hom, CommRingCat.comp_apply, Iso.symm_hom,
    Functor.mapIso_hom, Scheme.basicOpen_res_eq]

end

section

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} (f : (Spec R).Hom Y) [IsOpenImmersion f]

/-- **For an open immersion out of a spectrum, sections over the range are the ring itself.**

`AlgebraicGeometry.Scheme.ΓSpecIso` followed by `AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`, and
stated in that direction because that is the one its neighbour is stated in. This is the form a
caller holding an affine open cover is in: the cover gives the morphisms `Spec Rᵢ ⟶ Y` and asks
what a section over the `i`-th member is, and the answer is an element of `Rᵢ` and not a global
section of an auxiliary scheme. -/
def specΓIsoTop : R ≅ Γ(Y, f.opensRange) :=
  (Scheme.ΓSpecIso R).symm ≪≫ ΓIsoTop f

/-- **The image of `D(a)` is the distinguished open of the corresponding section over
`f.opensRange`**, for `a : R` and `f : Spec R ⟶ Y` an open immersion.

`AlgebraicGeometry.IsOpenImmersion.image_basicOpen_ΓIsoTop` at
`(AlgebraicGeometry.Scheme.ΓSpecIso R).inv a`, whose distinguished open in `Spec R` is
`PrimeSpectrum.basicOpen a` by `AlgebraicGeometry.basicOpen_eq_of_affine`.

**This is the statement that makes the isomorphism above usable rather than only true.** Without
it a caller who replaces a section over `f.opensRange` by an element of `R` has lost the open it
cuts out; with it the two descriptions are the same open of `Y`. -/
theorem image_primeSpectrum_basicOpen (a : R) :
    f ''ᵁ PrimeSpectrum.basicOpen a = Y.basicOpen ((specΓIsoTop f).hom a) := by
  have h : (specΓIsoTop f).hom = ((Scheme.ΓSpecIso R).symm ≪≫ ΓIsoTop f).hom := rfl
  rw [h, Iso.trans_hom, CommRingCat.comp_apply, ← image_basicOpen_ΓIsoTop, Iso.symm_hom,
    basicOpen_eq_of_affine]

end

end IsOpenImmersion

end AlgebraicGeometry

end
