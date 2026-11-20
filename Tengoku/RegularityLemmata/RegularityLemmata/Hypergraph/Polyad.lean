/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Hypergraph.Colored

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polyads, polyad blocks, and disc regularity

The level-`(j+1)` objects of hypergraph regularity relative to a level-`j` cell
assignment `κ : RSet j α → Fin K` — a coloring of the **unordered** `j`-element
sets, so cell data carries no ordered junk and polyads are automatically invariant
under permuting the tuple (`comp_perm_mem_polyadBlock`). Ordered face structures, if
ever needed, would be exposed separately, never as this API. The **polyad block** of
a key `P` collects the injective `(j+1)`-tuples each of whose lower-face `j`-sets
lies in the cell prescribed by `P`; blocks partition the injective tuples
(`sum_card_polyadBlock`). A **disc atom** further restricts every lower face to a
prescribed set of `j`-sets.

The regularity predicates over these test surfaces (the local per-parent
`IsDiscRegularAt`/`IsPolyadRegularAt`, their common-density globalizations, and the
repository-specific coarse `IsBlockUnionRegular`) live in
`RegularityLemmata/Hypergraph/PolyadRegularity.lean`; this file provides the set-level combinatorics
they consume, including the permutation transport of blocks and atoms
(`comp_perm_mem_polyadBlock`, `comp_perm_mem_discAtom`, and the cardinality/density
invariances).
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K : ℕ}

/-! ### Lower-face sets -/

/-- The vertex set of the `i`-th lower face of a `(j+1)`-tuple: the range of the
tuple that drops coordinate `i`.-/
def lowerFaceSet (v : Fin (j + 1) → α) (i : Fin (j + 1)) : Finset α :=
  tupleRange (lowerFace v i)

omit [Fintype α] in
/--
@isnad1 id=eq.0h4v.s6.bae7f09d938f from=translated src=- shape=9dc7efb9 vocab=f275b725
-/
theorem lowerFaceSet_eq_image_erase (v : Fin (j + 1) → α) (i : Fin (j + 1)) :
    lowerFaceSet v i = (Finset.univ.erase i).image v := by
  rw [lowerFaceSet, tupleRange]
  have himg : Finset.univ.image (i.succAbove) = Finset.univ.erase i := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Fin.succAbove_ne i x, trivial⟩
    · rintro ⟨hk, -⟩
      obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq hk
      exact ⟨x, rfl⟩
  rw [← himg, Finset.image_image]
  rfl

omit [Fintype α] in
/--
@isnad1 id=eq.1h4v.s6.112b91fef89e from=translated src=- shape=851cfd88 vocab=4eb0700b
-/
theorem card_lowerFaceSet {v : Fin (j + 1) → α} (hv : Function.Injective v)
    (i : Fin (j + 1)) : (lowerFaceSet v i).card = j :=
  card_tupleRange_of_injective (lowerFace_injective hv i)

/-- The `i`-th lower face of an injective tuple as an unordered `j`-set.-/
def lowerFaceRSet {v : Fin (j + 1) → α} (hv : Function.Injective v)
    (i : Fin (j + 1)) : RSet j α :=
  ⟨lowerFaceSet v i, card_lowerFaceSet hv i⟩

omit [Fintype α] in
/-- Permuting the tuple permutes its face sets.
@isnad1 id=eq.0h5v.s8.7b667f80eebd from=translated src=- shape=6c831a71 vocab=c766a3c6
-/
theorem lowerFaceSet_comp_perm (v : Fin (j + 1) → α) (σ : Equiv.Perm (Fin (j + 1)))
    (i : Fin (j + 1)) : lowerFaceSet (v ∘ σ) i = lowerFaceSet v (σ i) := by
  rw [lowerFaceSet_eq_image_erase, lowerFaceSet_eq_image_erase]
  have : (Finset.univ.erase i).image σ = Finset.univ.erase (σ i) := by
    rw [Finset.image_erase σ.injective, Finset.image_univ_of_surjective σ.surjective]
  rw [← this, Finset.image_image]

/-! ### Polyad blocks -/

/-- The **polyad block** of a key `P`: the injective `(j+1)`-tuples whose every
lower-face `j`-set is colored by the corresponding key entry. The face-cardinality
hypothesis is redundant given injectivity, but phrasing it dependently keeps the
filter computable (cf. `ColoredHypergraph.copyCount`).-/
def polyadBlock (κ : RSet j α → Fin K) (P : Fin (j + 1) → Fin K) :
    Finset (Fin (j + 1) → α) :=
  Finset.univ.filter fun v => Function.Injective v ∧
    ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
      κ ⟨lowerFaceSet v i, h⟩ = P i

/--
@isnad1 id=iff.0h6v.s7.337a93f37fe3 from=translated src=- shape=44c9fdbd vocab=cbdaa87a
-/
theorem mem_polyadBlock {κ : RSet j α → Fin K} {P : Fin (j + 1) → Fin K}
    {v : Fin (j + 1) → α} :
    v ∈ polyadBlock κ P ↔ Function.Injective v ∧
      ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
        κ ⟨lowerFaceSet v i, h⟩ = P i := by
  simp [polyadBlock]

/--
@isnad1 id=injectiv.1h6v.s7.1e4a14b40b3a from=translated src=- shape=de315adf vocab=a88d0029
-/
theorem injective_of_mem_polyadBlock {κ : RSet j α → Fin K}
    {P : Fin (j + 1) → Fin K} {v : Fin (j + 1) → α} (hv : v ∈ polyadBlock κ P) :
    Function.Injective v :=
  (mem_polyadBlock.mp hv).1

/-- Clean membership for injective tuples: the polyad is the tuple of face colors.
@isnad1 id=iff.1h6v.s7.131420ea7d3b from=translated src=- shape=640d669f vocab=d6301f88
-/
theorem mem_polyadBlock_iff_of_injective {κ : RSet j α → Fin K}
    {P : Fin (j + 1) → Fin K} {v : Fin (j + 1) → α} (hv : Function.Injective v) :
    v ∈ polyadBlock κ P ↔ ∀ i, κ (lowerFaceRSet hv i) = P i := by
  rw [mem_polyadBlock]
  constructor
  · intro h i
    exact h.2 i (card_lowerFaceSet hv i)
  · intro h
    exact ⟨hv, fun i _ => h i⟩

/-- The polyad key of an injective tuple: the tuple of its lower-face colors.-/
def polyadKey (κ : RSet j α → Fin K) {v : Fin (j + 1) → α}
    (hv : Function.Injective v) : Fin (j + 1) → Fin K :=
  fun i => κ (lowerFaceRSet hv i)

/--
@isnad1 id=mem.1h5v.s7.cc18863a9b0c from=translated src=- shape=7789ba29 vocab=c655317e
-/
theorem mem_polyadBlock_polyadKey (κ : RSet j α → Fin K) {v : Fin (j + 1) → α}
    (hv : Function.Injective v) : v ∈ polyadBlock κ (polyadKey κ hv) := by
  rw [mem_polyadBlock_iff_of_injective hv]
  intro i
  rfl

/--
@isnad1 id=eq.2h6v.s7.bac02efc6c48 from=translated src=- shape=94cc960d vocab=c655317e
-/
theorem polyadKey_eq_of_mem_polyadBlock {κ : RSet j α → Fin K}
    {P : Fin (j + 1) → Fin K} {v : Fin (j + 1) → α} (hv : Function.Injective v)
    (h : v ∈ polyadBlock κ P) : polyadKey κ hv = P :=
  funext ((mem_polyadBlock_iff_of_injective hv).mp h)

omit [Fintype α] in
/-- Reordering the tuple permutes its polyad key.
@isnad1 id=eq.2h6v.s9.a4514b220d0f from=translated src=- shape=73e137bc vocab=9e11d680
-/
theorem polyadKey_comp_perm (κ : RSet j α → Fin K) {v : Fin (j + 1) → α}
    (hv : Function.Injective v) (σ : Equiv.Perm (Fin (j + 1)))
    (hvσ : Function.Injective (v ∘ ⇑σ)) :
    polyadKey κ hvσ = polyadKey κ hv ∘ ⇑σ := by
  funext i
  exact congrArg κ (Subtype.ext (lowerFaceSet_comp_perm v σ i))

/--
@isnad1 id=disjoint.1h6v.s7.fd97dc9b77aa from=translated src=- shape=2f5a53eb vocab=c6a5d659
-/
theorem polyadBlock_disjoint {κ : RSet j α → Fin K} {P P' : Fin (j + 1) → Fin K}
    (h : P ≠ P') : Disjoint (polyadBlock κ P) (polyadBlock κ P') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_polyadBlock] at hv hv'
  refine h (funext fun i => ?_)
  rw [← hv.2 i (card_lowerFaceSet hv.1 i), hv'.2 i (card_lowerFaceSet hv.1 i)]

/--
@isnad1 id=eq.0h4v.s8.35f755e81f78 from=translated src=- shape=87c4f70a vocab=d3aa6682
-/
theorem biUnion_polyadBlock (κ : RSet j α → Fin K) :
    (Finset.univ : Finset (Fin (j + 1) → Fin K)).biUnion (polyadBlock κ)
      = injectiveTuples α (j + 1) := by
  ext v
  rw [Finset.mem_biUnion, mem_injectiveTuples]
  constructor
  · rintro ⟨P, -, hP⟩
    exact injective_of_mem_polyadBlock hP
  · intro hv
    refine ⟨fun i => κ (lowerFaceRSet hv i), Finset.mem_univ _, ?_⟩
    rw [mem_polyadBlock_iff_of_injective hv]
    intro i
    rfl

/-- **Partition of the injective tuples.** Every injective `(j+1)`-tuple lies in
exactly one polyad block, so the block cardinalities sum to the injective count.
@isnad1 id=eq.0h4v.s7.560ce263354e from=translated src=- shape=74300153 vocab=614d70b8
-/
theorem sum_card_polyadBlock (κ : RSet j α → Fin K) :
    ∑ P : Fin (j + 1) → Fin K, (polyadBlock κ P).card
      = injectiveTupleCount α (j + 1) := by
  classical
  rw [injectiveTupleCount, ← biUnion_polyadBlock κ]
  exact (Finset.card_biUnion fun P _ P' _ h => polyadBlock_disjoint h).symm

/-- **Permutation invariance**: reordering the tuple permutes the key. Unordered
cell data makes this automatic — the face sets themselves are permuted.
@isnad1 id=iff.0h7v.s9.f00de30d7683 from=translated src=- shape=6825d964 vocab=659b4d3a
-/
theorem comp_perm_mem_polyadBlock {κ : RSet j α → Fin K} {P : Fin (j + 1) → Fin K}
    {v : Fin (j + 1) → α} (σ : Equiv.Perm (Fin (j + 1))) :
    v ∘ σ ∈ polyadBlock κ P ↔ v ∈ polyadBlock κ (P ∘ ⇑σ⁻¹) := by
  constructor
  · intro h
    have hvσ : Function.Injective (v ∘ σ) := injective_of_mem_polyadBlock h
    have hv : Function.Injective v := (Equiv.injective_comp σ v).mp hvσ
    rw [mem_polyadBlock_iff_of_injective hv]
    intro i
    have hcol := (mem_polyadBlock_iff_of_injective hvσ).mp h (σ⁻¹ i)
    have hset : lowerFaceSet (v ∘ σ) (σ⁻¹ i) = lowerFaceSet v i := by
      rw [lowerFaceSet_comp_perm]
      exact congrArg (lowerFaceSet v) (σ.apply_symm_apply i)
    show κ (lowerFaceRSet hv i) = P (σ⁻¹ i)
    rw [← hcol]
    exact congrArg κ (Subtype.ext hset.symm)
  · intro h
    have hv : Function.Injective v := injective_of_mem_polyadBlock h
    have hvσ : Function.Injective (v ∘ σ) := (Equiv.injective_comp σ v).mpr hv
    rw [mem_polyadBlock_iff_of_injective hvσ]
    intro i
    have hcol := (mem_polyadBlock_iff_of_injective hv).mp h (σ i)
    have hset : lowerFaceSet (v ∘ σ) i = lowerFaceSet v (σ i) :=
      lowerFaceSet_comp_perm v σ i
    have hP : (P ∘ ⇑σ⁻¹) (σ i) = P i := congrArg P (σ.symm_apply_apply i)
    show κ (lowerFaceRSet hvσ i) = P i
    rw [← hP, ← hcol]
    exact congrArg κ (Subtype.ext hset)

/-! ### Disc atoms -/

/-- A **disc atom**: the tuples of the polyad block `key` whose every lower-face
`j`-set lies in the prescribed set family `P i`. Finer than any block or union of
blocks.-/
def discAtom (κ : RSet j α → Fin K) (key : Fin (j + 1) → Fin K)
    (P : Fin (j + 1) → Finset (RSet j α)) : Finset (Fin (j + 1) → α) :=
  (polyadBlock κ key).filter fun v =>
    ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
      (⟨lowerFaceSet v i, h⟩ : RSet j α) ∈ P i

/--
@isnad1 id=iff.0h7v.s8.2c56be9ad8cf from=translated src=- shape=819db22b vocab=b1c841bd
-/
theorem mem_discAtom {κ : RSet j α → Fin K} {key : Fin (j + 1) → Fin K}
    {P : Fin (j + 1) → Finset (RSet j α)} {v : Fin (j + 1) → α} :
    v ∈ discAtom κ key P ↔ v ∈ polyadBlock κ key ∧
      ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
        (⟨lowerFaceSet v i, h⟩ : RSet j α) ∈ P i := by
  simp [discAtom]

/-- Clean membership for tuples of the parent block.
@isnad1 id=iff.1h7v.s8.155dd0323da3 from=translated src=- shape=2d955654 vocab=a72305a1
-/
theorem mem_discAtom_iff_of_injective {κ : RSet j α → Fin K}
    {key : Fin (j + 1) → Fin K} {P : Fin (j + 1) → Finset (RSet j α)}
    {v : Fin (j + 1) → α} (hv : Function.Injective v) :
    v ∈ discAtom κ key P
      ↔ v ∈ polyadBlock κ key ∧ ∀ i, lowerFaceRSet hv i ∈ P i := by
  rw [mem_discAtom]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i
    exact h i (card_lowerFaceSet hv i)
  · intro h i _
    exact h i

/--
@isnad1 id=le.0h6v.s7.63772ccfa975 from=translated src=- shape=9f64c126 vocab=b0b11317
-/
theorem discAtom_subset_polyadBlock (κ : RSet j α → Fin K)
    (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (RSet j α)) :
    discAtom κ key P ⊆ polyadBlock κ key :=
  Finset.filter_subset _ _

/-- Unrestricted faces recover the whole block.
@isnad1 id=eq.0h5v.s6.bcfb55b730be from=translated src=- shape=e85397a9 vocab=517db70b
-/
theorem discAtom_univ (κ : RSet j α → Fin K) (key : Fin (j + 1) → Fin K) :
    discAtom κ key (fun _ => Finset.univ) = polyadBlock κ key := by
  rw [discAtom]
  exact Finset.filter_true_of_mem fun v _ i h => Finset.mem_univ _

/--
@isnad1 id=le.1h7v.s7.fc9c552af769 from=translated src=- shape=6d4fc8be vocab=146160ae
-/
theorem discAtom_mono {κ : RSet j α → Fin K} {key : Fin (j + 1) → Fin K}
    {P P' : Fin (j + 1) → Finset (RSet j α)} (h : ∀ i, P i ⊆ P' i) :
    discAtom κ key P ⊆ discAtom κ key P' := by
  intro v hv
  rw [mem_discAtom] at hv ⊢
  exact ⟨hv.1, fun i hi => h i (hv.2 i hi)⟩

/-- Restricting every face to the empty family empties the atom.
@isnad1 id=eq.0h5v.s6.7df8a96358b8 from=translated src=- shape=d90293fa vocab=950b1187
-/
theorem discAtom_empty_family (κ : RSet j α → Fin K) (key : Fin (j + 1) → Fin K) :
    discAtom κ key (fun _ => (∅ : Finset (RSet j α))) = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  rw [mem_discAtom] at hv
  have hinj := injective_of_mem_polyadBlock hv.1
  exact absurd (hv.2 0 (card_lowerFaceSet hinj 0)) (Finset.notMem_empty _)

/-! ### Permutation transport of atoms -/

/-- Permutation transport: reordering the tuple permutes the key and the face
families together.
@isnad1 id=iff.0h8v.s9.a80ababb7d93 from=translated src=- shape=76e6c226 vocab=f825a463
-/
theorem comp_perm_mem_discAtom {κ : RSet j α → Fin K} {key : Fin (j + 1) → Fin K}
    {P : Fin (j + 1) → Finset (RSet j α)} {v : Fin (j + 1) → α}
    (σ : Equiv.Perm (Fin (j + 1))) :
    v ∘ ⇑σ ∈ discAtom κ key P
      ↔ v ∈ discAtom κ (key ∘ ⇑σ⁻¹) (fun i => P (σ⁻¹ i)) := by
  constructor
  · intro h
    have hblock := (mem_discAtom.mp h).1
    have hvσ := injective_of_mem_polyadBlock hblock
    rw [mem_discAtom]
    refine ⟨(comp_perm_mem_polyadBlock σ).mp hblock, ?_⟩
    intro i hcard
    have hface := (mem_discAtom.mp h).2 (σ⁻¹ i) (card_lowerFaceSet hvσ (σ⁻¹ i))
    have hset : lowerFaceSet (v ∘ ⇑σ) (σ⁻¹ i) = lowerFaceSet v i := by
      rw [lowerFaceSet_comp_perm]
      exact congrArg (lowerFaceSet v) (σ.apply_symm_apply i)
    have hsub : (⟨lowerFaceSet (v ∘ ⇑σ) (σ⁻¹ i),
        card_lowerFaceSet hvσ (σ⁻¹ i)⟩ : RSet j α) = ⟨lowerFaceSet v i, hcard⟩ :=
      Subtype.ext hset
    exact hsub ▸ hface
  · intro h
    have hblock := (mem_discAtom.mp h).1
    have hv := injective_of_mem_polyadBlock hblock
    rw [mem_discAtom]
    refine ⟨(comp_perm_mem_polyadBlock σ).mpr hblock, ?_⟩
    intro i hcard
    have hface := (mem_discAtom.mp h).2 (σ i) (card_lowerFaceSet hv (σ i))
    have hset : lowerFaceSet (v ∘ ⇑σ) i = lowerFaceSet v (σ i) :=
      lowerFaceSet_comp_perm v σ i
    have hsub : (⟨lowerFaceSet v (σ i), card_lowerFaceSet hv (σ i)⟩ : RSet j α)
        = ⟨lowerFaceSet (v ∘ ⇑σ) i, hcard⟩ := Subtype.ext hset.symm
    have hP : P (σ⁻¹ (σ i)) = P i := congrArg P (σ.symm_apply_apply i)
    rw [hsub, hP] at hface
    exact hface

/-- Composing with `σ` on the right is a bijection between the transported atom and
the original one; cardinalities agree.
@isnad1 id=eq.0h7v.s8.53e19a9e4071 from=translated src=- shape=6df9179b vocab=d8ac8e19
-/
theorem card_discAtom_comp_perm (κ : RSet j α → Fin K) (key : Fin (j + 1) → Fin K)
    (P : Fin (j + 1) → Finset (RSet j α)) (σ : Equiv.Perm (Fin (j + 1))) :
    (discAtom κ (key ∘ ⇑σ⁻¹) (fun i => P (σ⁻¹ i))).card = (discAtom κ key P).card := by
  refine Finset.card_bij' (fun v _ => v ∘ ⇑σ) (fun w _ => w ∘ ⇑σ⁻¹)
    (fun v hv => (comp_perm_mem_discAtom σ).mpr hv) (fun w hw => ?_)
    (fun v _ => funext fun x => congrArg v (σ.apply_symm_apply x))
    (fun w _ => funext fun x => congrArg w (σ.symm_apply_apply x))
  refine (comp_perm_mem_discAtom σ).mp ?_
  have hcomp : (w ∘ ⇑σ⁻¹) ∘ ⇑σ = w := funext fun x => congrArg w (σ.symm_apply_apply x)
  rwa [hcomp]

/-- Filtered-cardinality version, for observables invariant under `σ`.
@isnad1 id=eq.1h8v.s9.df26626dcc72 from=translated src=- shape=229f715d vocab=b3b9922e
-/
theorem card_filter_discAtom_comp_perm (κ : RSet j α → Fin K)
    (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (RSet j α))
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs]
    (σ : Equiv.Perm (Fin (j + 1))) (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    ((discAtom κ (key ∘ ⇑σ⁻¹) (fun i => P (σ⁻¹ i))).filter obs).card
      = ((discAtom κ key P).filter obs).card := by
  refine Finset.card_bij' (fun v _ => v ∘ ⇑σ) (fun w _ => w ∘ ⇑σ⁻¹) (fun v hv => ?_)
    (fun w hw => ?_)
    (fun v _ => funext fun x => congrArg v (σ.apply_symm_apply x))
    (fun w _ => funext fun x => congrArg w (σ.symm_apply_apply x))
  · rw [Finset.mem_filter] at hv ⊢
    exact ⟨(comp_perm_mem_discAtom σ).mpr hv.1, (hobs v).mpr hv.2⟩
  · rw [Finset.mem_filter] at hw ⊢
    have hcomp : (w ∘ ⇑σ⁻¹) ∘ ⇑σ = w := funext fun x => congrArg w (σ.symm_apply_apply x)
    constructor
    · refine (comp_perm_mem_discAtom σ).mp ?_
      rw [hcomp]
      exact hw.1
    · have := hobs (w ∘ ⇑σ⁻¹)
      rw [hcomp] at this
      exact this.mp hw.2

/-- Density of a transported atom, for observables invariant under `σ`.
@isnad1 id=eq.1h8v.s9.82be9b9f3540 from=translated src=- shape=db5d7c48 vocab=7d92395c
-/
theorem densityOn_discAtom_comp_perm (κ : RSet j α → Fin K)
    (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (RSet j α))
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs]
    (σ : Equiv.Perm (Fin (j + 1))) (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    densityOn (discAtom κ (key ∘ ⇑σ⁻¹) (fun i => P (σ⁻¹ i))) obs
      = densityOn (discAtom κ key P) obs := by
  rw [densityOn, densityOn, card_filter_discAtom_comp_perm κ key P obs σ hobs,
    card_discAtom_comp_perm κ key P σ]

/-- Cardinality of a transported block.
@isnad1 id=eq.0h6v.s8.58f63edf6f31 from=translated src=- shape=b9081236 vocab=a48521de
-/
theorem card_polyadBlock_comp_perm (κ : RSet j α → Fin K)
    (key : Fin (j + 1) → Fin K) (σ : Equiv.Perm (Fin (j + 1))) :
    (polyadBlock κ (key ∘ ⇑σ⁻¹)).card = (polyadBlock κ key).card := by
  rw [← discAtom_univ κ key, ← discAtom_univ κ (key ∘ ⇑σ⁻¹)]
  exact card_discAtom_comp_perm κ key (fun _ => Finset.univ) σ

/-- Density of a transported block, for observables invariant under `σ`.
@isnad1 id=eq.1h7v.s9.c4d4bcc29183 from=translated src=- shape=e4f9f783 vocab=fbb718e8
-/
theorem densityOn_polyadBlock_comp_perm (κ : RSet j α → Fin K)
    (key : Fin (j + 1) → Fin K) (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs]
    (σ : Equiv.Perm (Fin (j + 1))) (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    densityOn (polyadBlock κ (key ∘ ⇑σ⁻¹)) obs = densityOn (polyadBlock κ key) obs := by
  rw [← discAtom_univ κ key, ← discAtom_univ κ (key ∘ ⇑σ⁻¹)]
  exact densityOn_discAtom_comp_perm κ key (fun _ => Finset.univ) obs σ hobs

/-! ### Tests and adversarial examples -/

section Tests

-- Level-1 cells over Fin 3: κ classifies singletons by whether they contain 2.
-- The block with both faces in cell 0 consists of the injective pairs valued in
-- {0, 1}: exactly 2 tuples.

end Tests

end RegularityLemmata
