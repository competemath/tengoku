/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.IsLocalHomeomorph
import Tengoku.Seed.Topology.Sets.OpenCover
import Tengoku.Seed.Topology.Sets.Opens

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sheets of a map, base change of a local homeomorphism, and locality on the target

`IsLocalHomeomorph f` says that every point of the source has *some* neighbourhood on which `f`
restricts to an open embedding. What a construction indexed by opens needs instead is the family
of all such opens together with the statement that it covers, and that is what is here:
`sheetOpens f` is the set of opens on which `f` is an open embedding, and
`IsLocalHomeomorph.sSup_sheetOpens` says its supremum is `⊤`.

**And the class is stable under base change**: `IsLocalHomeomorph.pullback_snd` carries it along an
arbitrary continuous map, at Mathlib's set-level fibre product `Function.Pullback`. The two
statements are independent of each other and share only their destination.

**And it is local on the target**:
`TopologicalSpace.IsOpenCover.isLocalHomeomorph_iff_restrictPreimage` says a continuous map is a
local homeomorphism exactly when its restriction over each member of an open cover of the target
is one. `Mathlib/Topology/LocalAtTarget.lean`'s module docstring enumerates seven properties of a
continuous map as local at the target and `IsLocalHomeomorph` is not one of them — `grep -n
'IsLocalHomeomorph'` over that file returns nothing at `v4.32.0`, so it is absent from that file's
declarations too — which is why the statement is here.

**The heading above read *The sheets of a map, as a family of opens* and the paragraph under it
ended at `IsLocalHomeomorph.sSup_sheetOpens` says its supremum is `⊤`, until 2026-09-14**, when the
base-change statement was appended. The heading is broadened rather than replaced: what it named is
still here.

**And it read *The sheets of a map as a family of opens, and base change of a local homeomorphism*
until 2026-09-14**, when the local-at-target statements were appended. Broadened again and again
not replaced; *as a family of opens* is dropped from the heading alone and the `## Main
definitions` entry it describes is untouched.

There is no analytic content here, so this file is a candidate for upstreaming; it lives in the
`Oka/Topology/` mirror of the Mathlib directory tree for that reason. Upstreaming to
`Mathlib/Topology/IsLocalHomeomorph.lean` costs that file **one** new import,
`Mathlib.Topology.Sets.OpenCover`, against a closure of 649 Mathlib modules that already contains
`Mathlib.Topology.Sets.Opens`, measured with
`python3 scripts/import_cost.py --target Mathlib.Topology.IsLocalHomeomorph`.

**That sentence read `costs that file **no** new imports` until 2026-09-14**, which was exact while
this file held the sheet material and the base change: `TopologicalSpace.IsOpenCover` is
`Mathlib.Topology.Sets.OpenCover`'s and neither of those needed it. **The 649 is unmoved and is not
what changed.**

## Where the local-at-target statement belongs, priced both ways

`Mathlib/Topology/LocalAtTarget.lean` is where the statements of this shape live. **Two different
figures count them and this file uses both, so they are told apart here rather than left to
collide.** Its module docstring enumerates **seven** properties as local at the target, and that is
the figure quoted above; `TopologicalSpace.IsOpenCover` in that file states **nine**
`…_iff_restrictPreimage` theorems at `v4.32.0`, which is the declaration count. **The two in the
gap are `isHomeomorph_iff_restrictPreimage` and `denseRange_iff_restrictPreimage`** — each a
theorem with no entry in the list — and `IsLocalHomeomorph` is in neither figure, which is what
matters here and is true of both.

It is **not** where this statement is put, and the reason is measured: that file's closure is 644
Mathlib modules and adding `Mathlib.Topology.IsLocalHomeomorph` to it costs **nine** — that module,
the five `Mathlib.Topology.OpenPartialHomeomorph.*`, `Mathlib.Topology.PartialHomeomorph.Defs`,
`Mathlib.Logic.Equiv.PartialEquiv` and `Mathlib.Topology.SeparatedMap` — against **one** in the
direction taken here. **The nine modules and the nine theorems are unrelated figures that happen to
agree**, which is said because nothing else in this file would stop a reader joining them.

**Mathlib settles it the same way for the neighbouring class.** `IsCoveringMap.restrictPreimage` is
a local-at-target statement and lives in `Mathlib/Topology/Covering/Basic.lean`, its property's own
file, and not in `Mathlib/Topology/LocalAtTarget.lean`. A Mathlib reviewer who prefers the other
home is disagreeing with a nine-module import and not with the statement.

## Why the `Opens` form rather than Mathlib's

`isLocalHomeomorph_iff_isOpenEmbedding_restrict` gives, for each `x`, some `U ∈ 𝓝 x` with
`IsOpenEmbedding (U.restrict f)`. A neighbourhood is not an open, and a consumer that glues over
a cover — `AlgebraicGeometry.LocallyRingedSpace.sheetIso` is the one this was written for — needs
opens and needs them as a *family with a supremum*, not one at a time. Passing through the
source of the `OpenPartialHomeomorph` that `IsLocalHomeomorph` unfolds to, which is open by
`OpenPartialHomeomorph.open_source`, avoids taking an interior and the proof that restricting an
open embedding to a smaller open is again one.

## Main definitions

- `sheetOpens`: the opens of the source on which the map is an open embedding.

## Main results

- `IsLocalHomeomorph.exists_mem_sheetOpens`: **every point lies in a sheet.**
- `IsLocalHomeomorph.sSup_sheetOpens`: **the sheets cover**, `sSup (sheetOpens f) = ⊤`.
- `IsLocalHomeomorph.pullback_snd`: **a local homeomorphism stays a local homeomorphism under base
  change along a continuous map.**
- `IsLocalHomeomorph.restrictPreimage_of_isOpen`: **a local homeomorphism restricted over an open
  subset of its target is one.**
- `TopologicalSpace.IsOpenCover.isLocalHomeomorph_of_restrictPreimage` and
  `TopologicalSpace.IsOpenCover.isLocalHomeomorph_iff_restrictPreimage`: **being a local
  homeomorphism is local on the target.**

## What is not here

* **Nothing about the fibres.** `sheetOpens f` is a set of opens and says nothing about how many
  of them meet a fibre; finiteness of the fibres is a separate hypothesis everywhere it is needed.
* **No sheet is distinguished and no choice is made.** `IsLocalHomeomorph.exists_mem_sheetOpens`
  is an existence statement; a consumer that wants one sheet per point chooses it itself.
* **No converse.** A map whose sheets cover *is* a local homeomorphism, by
  `isLocalHomeomorph_iff_isOpenEmbedding_restrict` and `Opens.isOpen`, but nothing below needs
  that direction and it is not stated.
* **Nothing about the sheets of a base change or of a restriction.**
  `IsLocalHomeomorph.pullback_snd` is stated through
  `isLocalHomeomorph_iff_isOpenEmbedding_restrict` and says nothing about how `sheetOpens` of the
  projection relates to `sheetOpens` of the map being base-changed, and the local-at-target
  statements say nothing about `sheetOpens` either; no part of this file meets another.

  **The last clause read *the two halves of this file do not meet* until 2026-09-14**, when a third
  part was appended and *two halves* stopped naming the file. Nothing about the base change is
  retired by it: the relation it denies between `sheetOpens` and `IsLocalHomeomorph.pullback_snd`
  is the same relation and is still not stated.
* **Nothing about a restriction over an arbitrary subset of the target.**
  `IsLocalHomeomorph.restrictPreimage_of_isOpen` asks its subset to be open and spends that
  hypothesis twice, once at each subtype inclusion. **The statement without it is true and is
  `IsLocalHomeomorph.pullback_snd` in disguise** — the subspace `f ⁻¹' s` is the base change of `f`
  along `s ↪ Y` — but reading it off that theorem needs a carrier identification between
  `Function.Pullback f Subtype.val` and `f ⁻¹' s` that nothing here writes, so the open case is
  proved directly instead. **Neither statement is derived from the other in this file.**
* **Nothing about `IsCoveringMap` at the target.** Mathlib's `IsCoveringMap.restrictPreimage`
  covers the forward direction for that class over an arbitrary subset, and the descent direction
  for it is a different statement about evenly-covered neighbourhoods that nothing here touches.
* **Nothing about the other three statements under `Oka/` whose conclusion is about
  `Function.Pullback.snd`.** A covering map base-changes by `IsCoveringMap.pullback_snd` and the
  fibres stay finite by `Function.Pullback.finite_fiber_snd` — both in
  `Oka/Topology/Covering/Basic.lean` — and a proper map stays proper by `IsProperMap.pullback_snd`
  in `Oka/Topology/Maps/Proper/Basic.lean`. **This file imports neither of those two modules and
  neither imports it**, each mirroring the Mathlib module its own statement belongs in.
-/

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/-- **The sheets of `f`**: the opens of the source on which `f` restricts to an open embedding. -/
def sheetOpens : Set (Opens X) := {V | IsOpenEmbedding ((V : Set X).domRestrict f)}

theorem mem_sheetOpens {V : Opens X} :
    V ∈ sheetOpens f ↔ IsOpenEmbedding ((V : Set X).domRestrict f) := Iff.rfl

/-- **Every point of the source lies in a sheet.**

The sheet produced is the source of the `OpenPartialHomeomorph` that `IsLocalHomeomorph` supplies,
which is open by construction — so no interior has to be taken. -/
theorem IsLocalHomeomorph.exists_mem_sheetOpens (hf : IsLocalHomeomorph f) (x : X) :
    ∃ V ∈ sheetOpens f, x ∈ V := by
  obtain ⟨e, hxe, he⟩ := hf x
  exact ⟨⟨e.source, e.open_source⟩, he ▸ e.isOpenEmbedding_restrict, hxe⟩

/-- **The sheets of a local homeomorphism cover its source.** -/
theorem IsLocalHomeomorph.sSup_sheetOpens (hf : IsLocalHomeomorph f) :
    sSup (sheetOpens f) = ⊤ := by
  refine top_le_iff.1 fun x _ ↦ ?_
  obtain ⟨V, hV, hxV⟩ := IsLocalHomeomorph.exists_mem_sheetOpens f hf x
  exact Opens.mem_sSup.2 ⟨V, hV, hxV⟩

section BaseChange

variable {f}
variable {Z : Type*} [TopologicalSpace Z] {g : Z → Y}

/-- **A local homeomorphism stays a local homeomorphism under base change along a continuous
map**, at Mathlib's set-level fibre product `Function.Pullback`. -/
theorem IsLocalHomeomorph.pullback_snd (hf : IsLocalHomeomorph f) (hg : Continuous g) :
    IsLocalHomeomorph (Function.Pullback.snd : f.Pullback g → Z) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro p
  obtain ⟨e, hmem, hfe⟩ := hf (Function.Pullback.fst p)
  have hfx : ∀ x, f x = e x := fun x ↦ congrFun hfe x
  have hcsnd : Continuous (Function.Pullback.snd : f.Pullback g → Z) :=
    continuous_snd.comp continuous_subtype_val
  have hUopen : IsOpen ((Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source) :=
    e.open_source.preimage (continuous_fst.comp continuous_subtype_val)
  have hTopen : IsOpen (g ⁻¹' e.target) := e.open_target.preimage hg
  refine ⟨_, hUopen.mem_nhds hmem, ?_⟩
  have hmapT : ∀ q : ((Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source),
      Function.Pullback.snd (q : f.Pullback g) ∈ g ⁻¹' e.target := by
    intro q
    have h1 : f (Function.Pullback.fst (q : f.Pullback g))
        = g (Function.Pullback.snd (q : f.Pullback g)) := (q : f.Pullback g).2
    change g (Function.Pullback.snd (q : f.Pullback g)) ∈ e.target
    rw [← h1, hfx]
    exact e.map_source q.2
  have hmapU : ∀ t : (g ⁻¹' e.target), f (e.symm (g (t : Z))) = g (t : Z) := by
    intro t
    rw [hfx]
    exact e.right_inv t.2
  have hmemU : ∀ t : (g ⁻¹' e.target),
      (⟨(e.symm (g (t : Z)), (t : Z)), hmapU t⟩ : f.Pullback g)
        ∈ (Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source :=
    fun t ↦ e.map_target t.2
  let φ : ((Function.Pullback.fst : f.Pullback g → X) ⁻¹' e.source) ≃ₜ (g ⁻¹' e.target) :=
    { toFun q := ⟨Function.Pullback.snd (q : f.Pullback g), hmapT q⟩
      invFun t := ⟨⟨(e.symm (g (t : Z)), (t : Z)), hmapU t⟩, hmemU t⟩
      left_inv q := by
        refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
        have h1 : f (Function.Pullback.fst (q : f.Pullback g))
            = g (Function.Pullback.snd (q : f.Pullback g)) := (q : f.Pullback g).2
        change e.symm (g (Function.Pullback.snd (q : f.Pullback g))) = _
        rw [← h1, hfx]
        exact e.left_inv q.2
      right_inv t := Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk (hcsnd.comp continuous_subtype_val) _
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_
          continuous_subtype_val) _) _
        exact (e.continuousOn_symm.comp hg.continuousOn fun t ht ↦ ht).domRestrict }
  exact hTopen.isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding

end BaseChange

/-! ### Being a local homeomorphism is local on the target -/

section LocalAtTarget

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {g : α → β}
variable {ι : Type*} {U : ι → Opens β}

/-- **A local homeomorphism restricted over an open subset of its target is a local
homeomorphism.**

`Subtype.val ∘ (s.restrictPreimage g) = g ∘ Subtype.val` holds by `rfl` — the two sides are the
same function of a point of `g ⁻¹' s`, read once in `s` and once in `β` — so the right-hand side
being a local homeomorphism is the hypothesis `IsLocalHomeomorph.of_comp` wants, and the left
factor it peels off is `Subtype.val` out of the open `s`.

**`s` is asked to be open and the hypothesis is not idle**: it is spent twice, once so that
`Subtype.val` out of `g ⁻¹' s` is an open embedding and once so that `Subtype.val` out of `s` is.
The statement without it is true and is `IsLocalHomeomorph.pullback_snd` in disguise, the subspace
`f ⁻¹' s` being the base change of `f` along `s ↪ β`; it is not derived from it here, because that
needs a carrier identification this file does not write. See this file's `## What is not here`. -/
theorem IsLocalHomeomorph.restrictPreimage_of_isOpen (H : IsLocalHomeomorph g) {s : Set β}
    (hs : IsOpen s) : IsLocalHomeomorph (s.restrictPreimage g) :=
  IsLocalHomeomorph.of_comp (g := (Subtype.val : s → β))
    (H.comp (hs.preimage H.continuous).isOpenEmbedding_subtypeVal.isLocalHomeomorph)
    hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph H.continuous.restrictPreimage

/-- **Being a local homeomorphism descends along an open cover of the target.**

`IsLocalHomeomorphOn` is a condition at each point of a set, so the conclusion is assembled one
point at a time: a point `x` has `g x` in some member `U i` of the cover, and what has to be
produced there is `IsLocalHomeomorphOn g (g ⁻¹' U i)`.

**The whole proof is `IsLocalHomeomorphOn.of_comp_right`.** The composite
`Subtype.val ∘ (U i).restrictPreimage g` is a local homeomorphism, being one open-subtype
inclusion after the hypothesis, and it is `g ∘ Subtype.val` by `rfl`; `of_comp_right` cancels the
right factor `Subtype.val` and returns the conclusion on its image, which `Subtype.range_coe`
identifies with `g ⁻¹' U i`.

**`Continuous g` is a hypothesis and it cannot be dropped.** Nothing else makes `g ⁻¹' U i` open,
and without that `Subtype.val` out of it is an embedding and not an open one. Mathlib's
`TopologicalSpace.IsOpenCover.isInducing_iff_restrictPreimage` and
`…isEmbedding_iff_restrictPreimage` carry the same hypothesis for the same reason, while
`…isClosedMap_iff_restrictPreimage` does not, because a closed map is not asked to be continuous
in the first place. A caller holding a morphism of spaces has the continuity for nothing. -/
theorem TopologicalSpace.IsOpenCover.isLocalHomeomorph_of_restrictPreimage (hU : IsOpenCover U)
    (hg : Continuous g) (H : ∀ i, IsLocalHomeomorph ((U i : Set β).restrictPreimage g)) :
    IsLocalHomeomorph g := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  intro x _
  obtain ⟨i, hi⟩ := hU.exists_mem (g x)
  have hopen : IsOpen (g ⁻¹' (U i : Set β)) := (U i).isOpen.preimage hg
  have hcomp : IsLocalHomeomorphOn
      (g ∘ (Subtype.val : (g ⁻¹' (U i : Set β)) → α)) Set.univ :=
    (((U i).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
      (H i)).isLocalHomeomorphOn
  have hval : IsLocalHomeomorphOn (Subtype.val : (g ⁻¹' (U i : Set β)) → α) Set.univ :=
    hopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hon := hcomp.of_comp_right hval
  rw [Set.image_univ, Subtype.range_coe] at hon
  exact hon x hi

/-- **Being a local homeomorphism is local on the target**, as the `iff` its two halves make.

The forward direction is `IsLocalHomeomorph.restrictPreimage_of_isOpen` at each member and the
backward one is `TopologicalSpace.IsOpenCover.isLocalHomeomorph_of_restrictPreimage`. The
`Continuous g` hypothesis is needed only by the backward direction; it is on the statement rather
than on that direction alone so that the two sides are an equivalence of conditions on a map
already known to be continuous, which is the shape
`TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage` has. -/
theorem TopologicalSpace.IsOpenCover.isLocalHomeomorph_iff_restrictPreimage (hU : IsOpenCover U)
    (hg : Continuous g) :
    IsLocalHomeomorph g ↔ ∀ i, IsLocalHomeomorph ((U i : Set β).restrictPreimage g) :=
  ⟨fun H i ↦ H.restrictPreimage_of_isOpen (U i).isOpen,
    hU.isLocalHomeomorph_of_restrictPreimage hg⟩

end LocalAtTarget
