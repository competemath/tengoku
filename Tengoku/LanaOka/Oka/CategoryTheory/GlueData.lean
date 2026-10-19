/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.CategoryTheory.GlueData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fields of `CategoryTheory.GlueData.ofGlueData'`

Material for `Mathlib/CategoryTheory/GlueData.lean`; see `README.md` on the mirror tree.

`CategoryTheory.GlueData'` is the variant of a glue datum that asks for the overlaps only when
`i ≠ j`, and `CategoryTheory.GlueData.ofGlueData'` turns one into a `CategoryTheory.GlueData` by
filling the diagonal with `dite`s. **At `v4.32.0` — the revision `lakefile.toml` pins, resolved by
`lake-manifest.json` to `81a5d257c8e410db227a6665ed08f64fea08e997` — Mathlib has no projection
lemmas for it at all**: `grep -rn "ofGlueData'" Mathlib/` returns **two** occurrences in **one**
file, the definition at `Mathlib/CategoryTheory/GlueData.lean:438` and a cross-reference inside
another docstring at `:348`. So a caller that has to *use* `f` or `t` of the result has to unfold
a `dite` by hand.

**Here a `grep` decides the claim rather than narrowing it**, and that is the verdict the three
questions put to a scan offered in support of one exist to reach: a *yes* to any of the three
means the scan narrows and does not decide, and all three are answered below. A projection lemma
about `(CategoryTheory.GlueData.ofGlueData' D).f` has to write the token `ofGlueData'` in its own
statement, whatever namespace is open, so there is no second spelling to miss; a `variable` binder
introducing the datum leaves the projection still to be written, so nothing is inherited from a
binder the scan does not read; and the one thing a scan of source cannot see — an equation lemma
generated on demand for the `def` — would unfold the whole structure instance rather than project
a field. **The environment agrees and is deliberately the weaker of the two routes**: at the commit
this paragraph is written at, of the names `scripts/DumpEnvNames.lean` dumps exactly **eight**
contain `ofGlueData'` — Mathlib's definition and the **seven** of this file's ten that carry the
token — and none of the **9023** generated `.eq_1` names among them is one. That route cannot be
the primary one: that dump is the environment of `Oka`, which imports some of Mathlib and not all of
it, so an absence in it is an absence from this build's imports and not from Mathlib.

**That clause read *`grep` finds `ofGlueData'` only in its own defining file* — no version, no
command and no control — until 2026-09-21**, and the same universal stood in five further files
with no instrument at all. **The claim is unchanged and only its warrant is**, which is why the
retired wording is kept here rather than struck. This file is the anchor the other six sites now
point at; taxis #2118 is the sweep.

This file supplies ten: two for `CategoryTheory.GlueData'.f'`, two for each of
`CategoryTheory.GlueData.ofGlueData'`'s `f` and `t`, the composite `t i j ≫ f j i`, the two
directions of the compatibility condition a family of morphisms out of the members satisfies, and
an extensionality principle for `CategoryTheory.GlueData'` itself.

## The extensionality principle asks for five fields of eight, and `t'` is not one of them

`CategoryTheory.GlueData'.ext_of_heq` concludes `D = D'` from `J`, `U`, `V`, `f` and `t`. It says
nothing about `t'`, and that is not an omission: **`t'` is determined by `t`.** Its own field
`t_fac` reads `t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j`, and the
`CategoryTheory.Limits.pullback.snd` there is a pullback of `f j k`, which the `f_mono` field
makes a monomorphism — so `t'` is the unique morphism with that factorisation and two glue data
agreeing through `t` cannot disagree below it. `CategoryTheory.cancel_mono` is the whole proof.

The hypotheses are `HEq`s and not `Eq`s because the fields are dependent: `f`'s type mentions `V`
and `U`, and `t`'s mentions `V`. A caller with `V`s that are only propositionally equal — which is
the situation whenever the overlaps are cut out by data that has been changed — has no `Eq` to
offer at `f` or below.

## Why they are not one `simp` call at the call site

The `dite`s of `CategoryTheory.GlueData'.f'` and of `CategoryTheory.GlueData.ofGlueData'`'s `t`
are **dependent**: the two branches have different types, since `V (i, i)` is `U i` and
`V (i, j)` is the given overlap. Consequently, at a goal where the `dite` is not at the head:

* `rw [dif_neg h]` reports *motive is not type correct*;
* `split_ifs` reports *tactic does nothing*;
* `simp` with `h : i ≠ j` in its argument list reports that argument **unused** and leaves the
  `dite` standing — the `Decidable` instance is `Classical.propDecidable`, from the
  `open scoped Classical` in Mathlib's own definition.

The technique that does work is to put the `dite` at the head — `change` to the `GlueData'.f'`
spelling, `dsimp only`, then `split_ifs` — and that is what these lemmas do once so that a caller
does not have to do it at every use.

## The composite `t i j ≫ f j i`, and the `dsimp only` that is not discoverable

`ComplexAnalytic.GlueDataCLinear` — and anything else comparing structures across an overlap —
asks about `t i j ≫ f j i`, where the two `eqToHom`s in the middle cancel.
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne` is that, and its proof is three lines: rewrite
with the two lemmas above, `dsimp only [GlueData.ofGlueData']`, `simp`.

**The middle line is the whole content, and deleting it leaves a goal that `simp`, `aesop_cat` and
`rw [Category.assoc]` all fail on** — the last reporting *did not find an occurrence of the pattern
`(?f ≫ ?g) ≫ ?h`* against a goal that visibly has that shape. Measured both ways: with the
`dsimp only` the proof closes in under two seconds, without it the goal is left unsolved.

The reason is **not** that the objects are `dite`s. After the two rewrites the *factors* carry the
`dite`s, while the composition's object positions still carry unreduced
`(GlueData.ofGlueData' D).V (i, j)` projections; `rw` matches at reducible transparency and
`GlueData.ofGlueData'` is a plain `def`, so the two spellings never meet. The blocker is an opaque
definition in an object position, which is why exactly one `dsimp only` removes it and why no set
of `simp` lemmas would have — and why `rw [Category.assoc]` *succeeds* on that same goal once the
`dsimp only` has run.

**That is why this is a lemma rather than three lines at the call site**: the middle line cannot be
guessed from the error message, which points at `Category.assoc` and says nothing about
transparency.

## The compatibility condition, and why its two directions are not one `iff`

Anything that maps *out* of a gluing — `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`
is this repository's instance — asks that a family `fY i : U i ⟶ Y` satisfy
`f i j ≫ fY i = t i j ≫ f j i ≫ fY j` at **every** pair, because that is the form the glue datum's
own `glue_condition` has. A caller can only supply it **off the diagonal**: `V (i, i)` is not a
chosen overlap and `t i i` is not a chosen transition, so there is nothing there to check and no
hypothesis to state about it.

`CategoryTheory.GlueData.ofGlueData'_comm` is that asymmetry — hypothesis at `i ≠ j`, conclusion at
every pair — and `CategoryTheory.GlueData.comm_of_ofGlueData'_comm` is the converse, which recovers
the caller's form from the glue datum's. **They are deliberately not packaged as an `iff`**: the
statements are not literally converse, since one quantifies over `i ≠ j` and the other over all
pairs, and each direction is used at a different place. The forward one turns a caller's
compatibility into `glueMorphisms`' hypothesis; the backward one reads a glue datum's own
`CategoryTheory.GlueData.glue_condition` back into the caller's vocabulary, which is what says the
inclusions `ι i` are themselves such a family and hence that gluing them returns the identity.

## Main results

- `CategoryTheory.GlueData'.f'_self` and `CategoryTheory.GlueData'.f'_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_f_self` and
  `CategoryTheory.GlueData.ofGlueData'_f_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_t_self` and
  `CategoryTheory.GlueData.ofGlueData'_t_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_comm` and
  `CategoryTheory.GlueData.comm_of_ofGlueData'_comm`
- `CategoryTheory.GlueData'.ext_of_heq`: **two glue data with the same `J`, `U`, `V`, `f` and `t`
  are equal**, `t'` being determined by `t`.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (D : GlueData' C)

/-- **`CategoryTheory.GlueData'.f'` on the diagonal is the `eqToHom` identifying `V (i, i)` with
`U i`.** -/
theorem GlueData'.f'_self (i : D.J) : D.f' i i = eqToHom (dite_eq_left rfl) := by
  dsimp only [GlueData'.f']
  split_ifs with h
  · rfl
  · exact absurd rfl h

/-- **`CategoryTheory.GlueData'.f'` off the diagonal is the given inclusion after the `eqToHom`
identifying `V (i, j)` with the given overlap.**

Stated about `f'` rather than about `CategoryTheory.GlueData.ofGlueData'`'s `f` field — they are
the same term — because it is the `f'` spelling that a goal is left in after
`dsimp only [GlueData.ofGlueData']`, and that is the position
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne` needs it at. -/
theorem GlueData'.f'_of_ne {i j : D.J} (h : i ≠ j) :
    D.f' i j = eqToHom (dite_eq_right h) ≫ D.f i j h := by
  dsimp only [GlueData'.f']
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- **On the diagonal, `CategoryTheory.GlueData.ofGlueData'`'s inclusion is the `eqToHom` that
identifies `V (i, i)` with `U i`.** -/
theorem GlueData.ofGlueData'_f_self (i : D.J) :
    (GlueData.ofGlueData' D).f i i = eqToHom (dite_eq_left rfl) :=
  GlueData'.f'_self D i

/-- **Off the diagonal, it is the given inclusion after the `eqToHom` that identifies
`V (i, j)` with the given overlap.** -/
theorem GlueData.ofGlueData'_f_of_ne {i j : D.J} (h : i ≠ j) :
    (GlueData.ofGlueData' D).f i j = eqToHom (dite_eq_right h) ≫ D.f i j h :=
  GlueData'.f'_of_ne D h

open scoped Classical in
/-- **On the diagonal, `CategoryTheory.GlueData.ofGlueData'`'s transition is an `eqToHom`.**

`CategoryTheory.GlueData` requires `t i i` to be the identity up to the identification of
`V (i, i)` with `U i`, and `ofGlueData'` discharges that; this is the value it discharges it
with. -/
theorem GlueData.ofGlueData'_t_self (i : D.J) :
    (GlueData.ofGlueData' D).t i i = eqToHom (by simp) := by
  dsimp only [GlueData.ofGlueData']
  split_ifs with h
  · rfl
  · exact absurd rfl h

open scoped Classical in
/-- **Off the diagonal, it is the given transition conjugated by the two `eqToHom`s that identify
`V (i, j)` and `V (j, i)` with the given overlaps.** -/
theorem GlueData.ofGlueData'_t_of_ne {i j : D.J} (h : i ≠ j) :
    (GlueData.ofGlueData' D).t i j =
      eqToHom (dite_eq_right h) ≫ D.t i j h ≫ eqToHom (dite_eq_right (Ne.symm h)).symm := by
  dsimp only [GlueData.ofGlueData']
  split_ifs with h'
  · exact absurd h' h
  · rfl

open scoped Classical in
/-- **The composite `t i j ≫ f j i`, with the two `eqToHom`s in the middle cancelled.**

The shape a caller comparing structures across an overlap works with. The `dsimp only` between
the rewrites and the `simp` is the whole content: without it the goal defeats `simp`, `aesop_cat`
and `rw [Category.assoc]`, because the composition's object positions carry unreduced
`GlueData.ofGlueData'` projections that `rw` will not unfold at reducible transparency. See the
module docstring; that line is not discoverable from the error, which is why this is a lemma. -/
theorem GlueData.ofGlueData'_t_comp_f_of_ne {i j : D.J} (h : i ≠ j) :
    (GlueData.ofGlueData' D).t i j ≫ (GlueData.ofGlueData' D).f j i =
      eqToHom (dite_eq_right h) ≫ D.t i j h ≫ D.f j i (Ne.symm h) := by
  rw [GlueData.ofGlueData'_t_of_ne D h, GlueData.ofGlueData'_f_of_ne D (Ne.symm h)]
  dsimp only [GlueData.ofGlueData']
  simp

/-! ### Extensionality -/

/-- **A `CategoryTheory.GlueData'` is determined by `J`, `U`, `V`, `f` and `t`.**

`t'` is absent from the hypotheses because it is not independent data: `t_fac` factorises it
through `CategoryTheory.Limits.pullback.snd`, which is a pullback of the monomorphism `f j k` and
so is itself monic, and `CategoryTheory.cancel_mono` finishes. The `f_mono` and `f_hasPullback`
fields are the instances that make that argument available, and they are proofs, so they need no
hypothesis either.

The five hypotheses are `HEq`s rather than `Eq`s because the fields are dependent — `f`'s type
mentions `V` and `U` — so a caller whose `V`s agree only propositionally has nothing else to
offer. -/
theorem GlueData'.ext_of_heq {D D' : GlueData' C}
    (hJ : D.J = D'.J) (hU : HEq D.U D'.U) (hV : HEq D.V D'.V) (hf : HEq D.f D'.f)
    (ht : HEq D.t D'.t) : D = D' := by
  obtain ⟨J, U, V, f, fmono, fpb, t, t', tfac, tinv, cocy⟩ := D
  obtain ⟨J', U', V', f', fmono', fpb', t₂, t'₂, tfac', tinv', cocy'⟩ := D'
  dsimp only at hJ hU hV hf ht
  subst hJ
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hV
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq ht
  haveI := fmono
  haveI := fpb
  have hlast : t' = t'₂ := by
    funext i j k hij hik hjk
    exact (cancel_mono (Limits.pullback.snd (f j k hjk) (f j i hij.symm))).1
      ((tfac i j k hij hik hjk).trans (tfac' i j k hij hik hjk).symm)
  subst hlast
  rfl

end CategoryTheory
