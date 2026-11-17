/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Regularity.Baire.Analytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The perfect-set theorem for analytic sets

Let `f : Baire → X` be continuous and suppose that its range is uncountable.  A finite Baire
prefix is called large when the image of its cylinder is uncountable.  The union of all countable
prefix images is countable.  Above a large prefix we may therefore choose two image points outside
that union, separate them in the Hausdorff target, and refine their preimages to two longer large
cylinders with disjoint images.

Iterating this construction gives a binary splitting system in Baire space whose sibling cylinder
images are disjoint.  The branch map from `Tree.Perfect`, followed by `f`, is consequently
continuous and injective.  Compactness of Cantor space and the Hausdorff target upgrade it to a
closed embedding.  Unfolding mathlib's definition of an analytic set then proves that every
uncountable analytic set contains this closed embedded Cantor copy.

The public theorem needs only a Hausdorff target.  No compatible metric, selected Polish
presentation, measurable-space instance, or cardinal-arithmetic shortcut occurs in its statement.
-/

open Set Topology

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

private theorem take_initialSegment_of_le {A : Type*} (x : ℕ → A) {m n : ℕ} (hmn : m ≤ n) :
    (initialSegment x n).take m = initialSegment x m := by
  apply List.ext_getElem
  · simp [length_initialSegment, hmn]
  · intro i hi₁ hi₂
    simp [initialSegment]

/-- The image of one basic Baire cylinder under `f`.-/
def prefixImage (f : (ℕ → ℕ) → X) (s : List ℕ) : Set X :=
  f '' bairePrefixCylinder s

/-- A Baire prefix is large for `f` when its cylinder has uncountable image.-/
def IsLargePrefix (f : (ℕ → ℕ) → X) (s : List ℕ) : Prop :=
  ¬(prefixImage f s).Countable

/-- Extending a finite prefix shrinks its Baire cylinder.
@isnad1 id=le.1h2v.s4.eb526b9cfeeb from=translated src=- shape=0a9e7fd2 vocab=2f0d3c21
-/
theorem bairePrefixCylinder_anti {s t : List ℕ} (hst : s <+: t) :
    bairePrefixCylinder t ⊆ bairePrefixCylinder s := by
  intro p hp
  change initialSegment p t.length = t at hp
  change initialSegment p s.length = s
  have hlen : s.length ≤ t.length := hst.length_le
  calc
    initialSegment p s.length = (initialSegment p t.length).take s.length :=
      (take_initialSegment_of_le p hlen).symm
    _ = t.take s.length := congrArg (fun r => r.take s.length) hp
    _ = s := (List.prefix_iff_eq_take.mp hst).symm

/-- Prefix images are antitone in the prefix order.
@isnad1 id=le.1h4v.s5.e476d0a3f382 from=translated src=- shape=e36ab37f vocab=05b637f9
-/
theorem prefixImage_anti (f : (ℕ → ℕ) → X) {s t : List ℕ} (hst : s <+: t) :
    prefixImage f t ⊆ prefixImage f s :=
  image_mono (bairePrefixCylinder_anti hst)

/-- If a longer prefix is large, then every shorter prefix is large.
@isnad1 id=islargep.2h4v.s4.8f66da1cad8b from=translated src=- shape=2ad9da40 vocab=d469727c
-/
theorem IsLargePrefix.of_prefix (f : (ℕ → ℕ) → X) {s t : List ℕ} (hst : s <+: t)
    (ht : IsLargePrefix f t) : IsLargePrefix f s := by
  intro hs
  exact ht (hs.mono (prefixImage_anti f hst))

/-- Large prefixes form a natural-number tree.-/
def largePrefixTree (f : (ℕ → ℕ) → X) : Descriptive.tree ℕ where
  val := {s | IsLargePrefix f s}
  property := by
    intro s a hs
    exact IsLargePrefix.of_prefix f ⟨[a], rfl⟩ hs

/-- The union of the images of all cylinders having countable image.-/
def countableLocalImage (f : (ℕ → ℕ) → X) : Set X :=
  ⋃ (s : List ℕ) (_ : (prefixImage f s).Countable), prefixImage f s

/-- The exceptional union of all countable local images is countable.
@isnad1 id=countabl.0h2v.s3.618b9f3d3d3e from=translated src=- shape=147c59f5 vocab=18b70427
-/
theorem countable_countableLocalImage (f : (ℕ → ℕ) → X) :
    (countableLocalImage f).Countable := by
  unfold countableLocalImage
  exact countable_iUnion fun s => countable_iUnion fun hs => hs

/-- A local image containing a point outside the exceptional union is large.
@isnad1 id=islargep.2h4v.s5.bbfca20934f0 from=translated src=- shape=355c8e0f vocab=ab46f6fb
-/
theorem isLargePrefix_of_mem_not_countableLocalImage (f : (ℕ → ℕ) → X)
    {s : List ℕ} {x : X} (hx : x ∈ prefixImage f s) (hxbad : x ∉ countableLocalImage f) :
    IsLargePrefix f s := by
  intro hs
  exact hxbad (mem_iUnion_of_mem s (mem_iUnion_of_mem hs hx))

/-- Removing the exceptional countable union from a large local image leaves an uncountable set.
@isnad1 id=not.1h3v.s4.39d928202d20 from=translated src=- shape=0dd09506 vocab=ab878789
-/
theorem not_countable_prefixImage_sdiff_countableLocalImage (f : (ℕ → ℕ) → X)
    {s : List ℕ} (hs : IsLargePrefix f s) :
    ¬(prefixImage f s \ countableLocalImage f).Countable := by
  intro hdiff
  exact hs (hdiff.of_sdiff (countable_countableLocalImage f))

private theorem nontrivial_of_not_countable {A : Set X} (hA : ¬A.Countable) : A.Nontrivial := by
  by_contra htriv
  apply hA
  by_cases hne : A.Nonempty
  · rcases hne with ⟨x, hx⟩
    exact (countable_singleton x).mono fun y hy => by
      have hyx : y = x := by
        by_contra h
        exact htriv ⟨y, hy, x, hx, h⟩
      simp [hyx]
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact countable_empty

/-- Every large prefix image is nonempty.
@isnad1 id=nonempty.1h3v.s4.0c54941d691e from=translated src=- shape=2158d41b vocab=308d0a8a
-/
theorem IsLargePrefix.prefixImage_nonempty (f : (ℕ → ℕ) → X) {s : List ℕ}
    (hs : IsLargePrefix f s) : (prefixImage f s).Nonempty := by
  by_contra hne
  apply hs
  rw [not_nonempty_iff_eq_empty.mp hne]
  exact countable_empty

private theorem exists_large_extension_image_subset [TopologicalSpace X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) {s : List ℕ} {p : ℕ → ℕ} {U : Set X}
    (hps : p ∈ bairePrefixCylinder s) (hpbad : f p ∉ countableLocalImage f)
    (hUopen : IsOpen U) (hfpU : f p ∈ U) :
    ∃ t : List ℕ, s <+: t ∧ s.length < t.length ∧ IsLargePrefix f t ∧
      prefixImage f t ⊆ U := by
  have hpreopen : IsOpen (f ⁻¹' U) := hUopen.preimage hf
  rcases (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open
      hfpU hpreopen with ⟨C, ⟨q, n, rfl⟩, hpC, hCsub⟩
  have hCsub' : PiNat.cylinder p n ⊆ f ⁻¹' U := by
    rw [PiNat.mem_cylinder_iff_eq.mp hpC]
    exact hCsub
  let m := max n (s.length + 1)
  let t := initialSegment p m
  have hsm : s.length ≤ m :=
    (Nat.le_succ s.length).trans (Nat.le_max_right n (s.length + 1))
  have hst : s <+: t := by
    have hprefix := Tree.initialSegment_prefix p hsm
    change initialSegment p s.length = s at hps
    simpa [t, hps] using hprefix
  have hslt : s.length < t.length := by
    calc
      s.length < m :=
        (Nat.lt_succ_self s.length).trans_le (Nat.le_max_right n (s.length + 1))
      _ = t.length := by simp [t]
  have htC : bairePrefixCylinder t ⊆ PiNat.cylinder p n := by
    change bairePrefixCylinder (initialSegment p m) ⊆ PiNat.cylinder p n
    rw [bairePrefixCylinder_initialSegment]
    exact PiNat.cylinder_anti p (Nat.le_max_left n (s.length + 1))
  have hlarge : IsLargePrefix f t := by
    apply isLargePrefix_of_mem_not_countableLocalImage f
    · exact ⟨p, by
          change p ∈ bairePrefixCylinder (initialSegment p m)
          rw [bairePrefixCylinder_initialSegment]
          exact PiNat.self_mem_cylinder p m, rfl⟩
    · exact hpbad
  refine ⟨t, hst, hslt, hlarge, ?_⟩
  rintro x ⟨r, hr, rfl⟩
  exact hCsub' (htC hr)

private structure LargeImageSplit [TopologicalSpace X] (f : (ℕ → ℕ) → X)
    (s : largePrefixTree f) where
  left : largePrefixTree f
  right : largePrefixTree f
  prefix_left : s.1 <+: left.1
  prefix_right : s.1 <+: right.1
  length_lt_left : s.1.length < left.1.length
  length_lt_right : s.1.length < right.1.length
  incompatible : Tree.AreIncompatible left.1 right.1
  image_disjoint : Disjoint (prefixImage f left.1) (prefixImage f right.1)

private theorem nonempty_largeImageSplit [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) :
    Nonempty (LargeImageSplit f s) := by
  have hremain := not_countable_prefixImage_sdiff_countableLocalImage f s.2
  rcases nontrivial_of_not_countable hremain with
    ⟨x, ⟨hx, hxbad⟩, y, ⟨hy, hybad⟩, hxy⟩
  rcases hx with ⟨p, hp, rfl⟩
  rcases hy with ⟨q, hq, rfl⟩
  rcases t2_separation hxy with ⟨U, V, hUopen, hVopen, hfpU, hfqV, hUV⟩
  rcases exists_large_extension_image_subset f hf hp hxbad hUopen hfpU with
    ⟨t, hst, hslt, htlarge, htU⟩
  rcases exists_large_extension_image_subset f hf hq hybad hVopen hfqV with
    ⟨u, hsu, hsul, hularge, huV⟩
  have hdis : Disjoint (prefixImage f t) (prefixImage f u) := hUV.mono htU huV
  have hinc : Tree.AreIncompatible t u := by
    constructor
    · intro htu
      rcases hularge.prefixImage_nonempty f with ⟨z, hz⟩
      exact Set.disjoint_left.mp hdis (prefixImage_anti f htu hz) hz
    · intro hut
      rcases htlarge.prefixImage_nonempty f with ⟨z, hz⟩
      exact Set.disjoint_left.mp hdis hz (prefixImage_anti f hut hz)
  exact ⟨{
    left := ⟨t, htlarge⟩
    right := ⟨u, hularge⟩
    prefix_left := hst
    prefix_right := hsu
    length_lt_left := hslt
    length_lt_right := hsul
    incompatible := hinc
    image_disjoint := hdis
  }⟩

/-- A coherent binary splitting system whose sibling Baire cylinders have disjoint images under
`f`.  The underlying source nodes are large, hence all their local images remain uncountable.-/
structure ImageSplittingSystem [TopologicalSpace X] (f : (ℕ → ℕ) → X) where
  /-- The selected Baire prefix at each finite binary address.-/
  node : List Bool → List ℕ
  /-- Every selected local image is uncountable.-/
  node_large : ∀ s, IsLargePrefix f (node s)
  /-- Every selected child extends its parent.-/
  node_prefix_child : ∀ s b, node s <+: node (s ++ [b])
  /-- Every selected child is a strict extension.-/
  node_length_lt_child : ∀ s b, (node s).length < (node (s ++ [b])).length
  /-- Sibling source prefixes are incompatible.-/
  children_incompatible : ∀ s,
    Tree.AreIncompatible (node (s ++ [false])) (node (s ++ [true]))
  /-- Sibling cylinder images are disjoint; this is the invariant that makes `f` injective on the
  selected Cantor branches.-/
  children_image_disjoint : ∀ s,
    Disjoint (prefixImage f (node (s ++ [false])))
      (prefixImage f (node (s ++ [true])))

namespace ImageSplittingSystem

variable [TopologicalSpace X] {f : (ℕ → ℕ) → X} (S : ImageSplittingSystem f)

/-- Forgetting target-image disjointness gives the v1.28 binary splitting system in the large
prefix tree.-/
def toBinarySplittingSystem : Tree.BinarySplittingSystem (largePrefixTree f) where
  node := S.node
  node_mem := S.node_large
  node_prefix_child := S.node_prefix_child
  node_length_lt_child := S.node_length_lt_child
  children_incompatible := S.children_incompatible

/-- Sibling image disjointness with the two Boolean values in either order.
@isnad1 id=disjoint.1h6v.s6.7504796fcc04 from=translated src=- shape=78d171b3 vocab=b70b101a
-/
theorem children_image_disjoint_of_ne (s : List Bool) {b c : Bool} (hbc : b ≠ c) :
    Disjoint (prefixImage f (S.node (s ++ [b])))
      (prefixImage f (S.node (s ++ [c]))) := by
  cases b <;> cases c
  · exact (hbc rfl).elim
  · exact S.children_image_disjoint s
  · exact (S.children_image_disjoint s).symm
  · exact (hbc rfl).elim

/-- The source branch selected by the underlying binary splitting system.-/
def sourceBranch : (ℕ → Bool) → (ℕ → ℕ) :=
  S.toBinarySplittingSystem.branchMap

/-- Every selected source branch lies in the cylinder of each selected node on its binary path.
@isnad1 id=mem.0h5v.s5.8bd447326d75 from=translated src=- shape=c7de85e5 vocab=572d7fd2
-/
theorem sourceBranch_mem_nodeCylinder (q : ℕ → Bool) (m : ℕ) :
    S.sourceBranch q ∈ bairePrefixCylinder (S.node (initialSegment q m)) := by
  change initialSegment (S.sourceBranch q) (S.node (initialSegment q m)).length =
    S.node (initialSegment q m)
  exact (S.toBinarySplittingSystem.node_eq_initialSegment_branchMap q m).symm

/-- The Cantor map into the target is `f` after the selected Baire branch map.-/
def cantorMap : (ℕ → Bool) → X :=
  f ∘ S.sourceBranch

/-- The target Cantor map is continuous whenever the presenting map is continuous.
@isnad1 id=continuo.1h3v.s5.5cad967d7a52 from=translated src=- shape=e3ee57f5 vocab=1d5541f8
-/
theorem continuous_cantorMap (hf : Continuous f) : Continuous S.cantorMap :=
  hf.comp S.toBinarySplittingSystem.continuous_branchMap

/-- Disjoint sibling images make the target Cantor map injective.
@isnad1 id=injectiv.0h3v.s4.c04947e6fe03 from=translated src=- shape=188dbdc7 vocab=1521b73a
-/
theorem injective_cantorMap : Function.Injective S.cantorMap := by
  intro q r hqr
  have hsegments : ∀ n, initialSegment q n = initialSegment r n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hbit : q n = r n := by
          by_contra hbit
          have hdis := S.children_image_disjoint_of_ne (initialSegment q n) hbit
          have hqmem : S.cantorMap q ∈
              prefixImage f (S.node (initialSegment q n ++ [q n])) := by
            refine ⟨S.sourceBranch q, ?_, rfl⟩
            simpa [initialSegment_succ] using S.sourceBranch_mem_nodeCylinder q (n + 1)
          have hrmem : S.cantorMap r ∈
              prefixImage f (S.node (initialSegment q n ++ [r n])) := by
            refine ⟨S.sourceBranch r, ?_, rfl⟩
            simpa [initialSegment_succ, ih] using S.sourceBranch_mem_nodeCylinder r (n + 1)
          exact Set.disjoint_left.mp hdis hqmem (hqr ▸ hrmem)
        simp [initialSegment_succ, ih, hbit]
  funext n
  have h := hsegments (n + 1)
  rw [initialSegment_succ, initialSegment_succ, hsegments n] at h
  simpa using List.append_cancel_left h

/-- The target Cantor map has range contained in the range of the presenting map.
@isnad1 id=le.0h3v.s5.44e3944d6c62 from=translated src=- shape=3a63ca8b vocab=a17d5c46
-/
theorem range_cantorMap_subset_range : range S.cantorMap ⊆ range f := by
  rintro _ ⟨q, rfl⟩
  exact ⟨S.sourceBranch q, rfl⟩

/-- In a Hausdorff target, the selected target map is a closed embedding.
@isnad1 id=isclosed.1h3v.s5.86917aa9b6b4 from=translated src=- shape=5a6fd0f7 vocab=7506a4f9
-/
theorem isClosedEmbedding_cantorMap [T2Space X] (hf : Continuous f) :
    IsClosedEmbedding S.cantorMap :=
  (S.continuous_cantorMap hf).isClosedEmbedding S.injective_cantorMap

/-- The selected target map is a topological embedding.
@isnad1 id=isembedd.1h3v.s5.8ea8d9308fb6 from=translated src=- shape=5a6fd0f7 vocab=727a81bf
-/
theorem isEmbedding_cantorMap [T2Space X] (hf : Continuous f) : IsEmbedding S.cantorMap :=
  (S.isClosedEmbedding_cantorMap hf).isEmbedding

/-- The selected Cantor range is closed in a Hausdorff target.
@isnad1 id=isclosed.1h3v.s5.cd5dea26d380 from=translated src=- shape=20abf4ea vocab=a9e6c9e6
-/
theorem isClosed_range_cantorMap [T2Space X] (hf : Continuous f) :
    IsClosed (range S.cantorMap) :=
  (S.isClosedEmbedding_cantorMap hf).isClosed_range

/-- The selected target range is homeomorphic to Cantor space.-/
noncomputable def cantorHomeomorph [T2Space X] (hf : Continuous f) :
    (ℕ → Bool) ≃ₜ range S.cantorMap :=
  (S.isEmbedding_cantorMap hf).toHomeomorph

end ImageSplittingSystem

private noncomputable def chosenLargeImageSplit [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) :
    LargeImageSplit f s :=
  Classical.choice (nonempty_largeImageSplit f hf s)

private noncomputable def nextLargeNode [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) (b : Bool) :
    largePrefixTree f :=
  if b then (chosenLargeImageSplit f hf s).right else (chosenLargeImageSplit f hf s).left

private theorem prefix_nextLargeNode [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) (b : Bool) :
    s.1 <+: (nextLargeNode f hf s b).1 := by
  cases b <;> simp [nextLargeNode, (chosenLargeImageSplit f hf s).prefix_left,
    (chosenLargeImageSplit f hf s).prefix_right]

private theorem length_lt_nextLargeNode [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) (b : Bool) :
    s.1.length < (nextLargeNode f hf s b).1.length := by
  cases b <;> simp [nextLargeNode, (chosenLargeImageSplit f hf s).length_lt_left,
    (chosenLargeImageSplit f hf s).length_lt_right]

private theorem nextLargeNodes_incompatible [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) :
    Tree.AreIncompatible (nextLargeNode f hf s false).1 (nextLargeNode f hf s true).1 := by
  simpa [nextLargeNode] using (chosenLargeImageSplit f hf s).incompatible

private theorem nextLargeNodes_image_disjoint [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (s : largePrefixTree f) :
    Disjoint (prefixImage f (nextLargeNode f hf s false).1)
      (prefixImage f (nextLargeNode f hf s true).1) := by
  simpa [nextLargeNode] using (chosenLargeImageSplit f hf s).image_disjoint

private theorem prefixImage_nil (f : (ℕ → ℕ) → X) : prefixImage f [] = range f := by
  ext x
  constructor
  · rintro ⟨p, _, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, by simp [bairePrefixCylinder], rfl⟩

private theorem root_mem_largePrefixTree (f : (ℕ → ℕ) → X)
    (hunc : ¬(range f).Countable) : [] ∈ largePrefixTree f := by
  change IsLargePrefix f []
  rw [IsLargePrefix, prefixImage_nil]
  exact hunc

private noncomputable def largeNodeAt [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (hunc : ¬(range f).Countable)
    (s : List Bool) : largePrefixTree f :=
  s.foldl (nextLargeNode f hf) ⟨[], root_mem_largePrefixTree f hunc⟩

private theorem largeNodeAt_append [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (hunc : ¬(range f).Countable)
    (s : List Bool) (b : Bool) :
    largeNodeAt f hf hunc (s ++ [b]) = nextLargeNode f hf (largeNodeAt f hf hunc s) b := by
  simp [largeNodeAt]

/-- An uncountable continuous Baire image in a Hausdorff space admits a coherent splitting system
whose sibling cylinder images are disjoint.  Choice is confined to the existential constructor;
no canonical selector is exported.
@isnad1 id=nonempty.2h2v.s5.1a712576fa74 from=translated src=- shape=acc35c7f vocab=0d1af6e8
-/
theorem exists_imageSplittingSystem [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (hunc : ¬(range f).Countable) :
    Nonempty (ImageSplittingSystem f) := by
  let S : ImageSplittingSystem f :=
    { node := fun s => (largeNodeAt f hf hunc s).1
      node_large := fun s => (largeNodeAt f hf hunc s).2
      node_prefix_child := fun s b => by
        rw [largeNodeAt_append]
        exact prefix_nextLargeNode f hf (largeNodeAt f hf hunc s) b
      node_length_lt_child := fun s b => by
        rw [largeNodeAt_append]
        exact length_lt_nextLargeNode f hf (largeNodeAt f hf hunc s) b
      children_incompatible := fun s => by
        rw [largeNodeAt_append, largeNodeAt_append]
        exact nextLargeNodes_incompatible f hf (largeNodeAt f hf hunc s)
      children_image_disjoint := fun s => by
        rw [largeNodeAt_append, largeNodeAt_append]
        exact nextLargeNodes_image_disjoint f hf (largeNodeAt f hf hunc s) }
  exact ⟨S⟩

/-- An uncountable continuous image of Baire space contains a closed embedded copy of Cantor
space.  Its range is explicitly contained in the original continuous range.
@isnad1 id=ex.2h2v.s6.356c5206673c from=translated src=- shape=24b53f99 vocab=c54432f8
-/
theorem exists_isClosedEmbedding_cantor_of_continuous_range [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (hunc : ¬(range f).Countable) :
    ∃ e : (ℕ → Bool) → X, IsClosedEmbedding e ∧ range e ⊆ range f := by
  rcases exists_imageSplittingSystem f hf hunc with ⟨S⟩
  exact ⟨S.cantorMap, S.isClosedEmbedding_cantorMap hf, S.range_cantorMap_subset_range⟩

/-- Perfect-set theorem for analytic sets: every uncountable analytic subset of a Hausdorff space
contains a closed embedded copy of Cantor space.
@isnad1 id=ex.2h2v.s5.b156aad31b1e from=translated src=- shape=e24f25da vocab=f6ba174a
-/
theorem _root_.MeasureTheory.AnalyticSet.exists_isClosedEmbedding_cantor
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s)
    (hunc : ¬s.Countable) :
    ∃ e : (ℕ → Bool) → X, IsClosedEmbedding e ∧ range e ⊆ s := by
  rw [MeasureTheory.AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, hfs⟩
  · exact (hunc countable_empty).elim
  · have hunc' : ¬(range f).Countable := by simpa [hfs] using hunc
    rcases exists_isClosedEmbedding_cantor_of_continuous_range f hf hunc' with
      ⟨e, he, herange⟩
    exact ⟨e, he, herange.trans (by simp [hfs])⟩

/-- Continuous-injection formulation of the analytic perfect-set theorem.
@isnad1 id=ex.2h2v.s6.4dc0e89fa64c from=translated src=- shape=4ea23ea0 vocab=65730c59
-/
theorem _root_.MeasureTheory.AnalyticSet.exists_continuous_injective_cantor
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s)
    (hunc : ¬s.Countable) :
    ∃ e : (ℕ → Bool) → X, Continuous e ∧ Function.Injective e ∧ range e ⊆ s := by
  rcases hs.exists_isClosedEmbedding_cantor hunc with ⟨e, he, hes⟩
  exact ⟨e, he.continuous, he.isEmbedding.injective, hes⟩

/-- Embedding formulation of the analytic perfect-set theorem.
@isnad1 id=ex.2h2v.s5.eb59d960c699 from=translated src=- shape=e24f25da vocab=299ab918
-/
theorem _root_.MeasureTheory.AnalyticSet.exists_isEmbedding_cantor
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s)
    (hunc : ¬s.Countable) :
    ∃ e : (ℕ → Bool) → X, IsEmbedding e ∧ range e ⊆ s := by
  rcases hs.exists_isClosedEmbedding_cantor hunc with ⟨e, he, hes⟩
  exact ⟨e, he.isEmbedding, hes⟩

/-- Closed-range and homeomorphic-copy formulation of the analytic perfect-set theorem.
@isnad1 id=ex.2h2v.s6.3882c7250f62 from=translated src=- shape=5be866a7 vocab=7d2ad917
-/
theorem _root_.MeasureTheory.AnalyticSet.exists_closed_cantor_copy
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s)
    (hunc : ¬s.Countable) :
    ∃ C : Set X, C ⊆ s ∧ IsClosed C ∧ Nonempty ((ℕ → Bool) ≃ₜ C) := by
  rcases hs.exists_isClosedEmbedding_cantor hunc with ⟨e, he, hes⟩
  exact ⟨range e, hes, he.isClosed_range, ⟨he.isEmbedding.toHomeomorph⟩⟩

/-- Baire-space specialization of the analytic perfect-set theorem.
@isnad1 id=ex.2h1v.s6.4f0414c7ae8a from=translated src=- shape=d14715ff vocab=1354ad20
-/
theorem analyticSet_exists_isClosedEmbedding_cantor_baire {s : Set (ℕ → ℕ)}
    (hs : MeasureTheory.AnalyticSet s) (hunc : ¬s.Countable) :
    ∃ e : (ℕ → Bool) → (ℕ → ℕ), IsClosedEmbedding e ∧ range e ⊆ s :=
  hs.exists_isClosedEmbedding_cantor hunc

/-- Cantor-space specialization of the analytic perfect-set theorem.
@isnad1 id=ex.2h1v.s6.1c23ec33cc9c from=translated src=- shape=34e0a588 vocab=1354ad20
-/
theorem analyticSet_exists_isClosedEmbedding_cantor_cantor {s : Set (ℕ → Bool)}
    (hs : MeasureTheory.AnalyticSet s) (hunc : ¬s.Countable) :
    ∃ e : (ℕ → Bool) → (ℕ → Bool), IsClosedEmbedding e ∧ range e ⊆ s :=
  hs.exists_isClosedEmbedding_cantor hunc

end DescriptiveSetTheory
