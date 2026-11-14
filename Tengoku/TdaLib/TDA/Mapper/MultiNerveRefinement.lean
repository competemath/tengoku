import Tengoku.TdaLib.TDA.Mapper.MultiNerve
import Tengoku.TdaLib.TDA.Mapper.Tower
import Tengoku.TdaLib.TDA.Topology.MultiNerveMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Refinement maps of MultiNerve Mappers

A selected refinement `R : Refinement U V` of target families induces the selected refinement
`componentRefinement f R` of path-component pullback covers, and hence the generic multinerve
map `multiNerveMapperMap f R : multiNerveMapper f U → multiNerveMapper f V`. It preserves
identity and composition, is monotone for the face order, sends vertex cells to vertex cells,
and lies over the ordinary Mapper map `mapperMap f R` under the projections onto ordinary
Mapper. A coherent cover tower therefore gives MultiNerve Mapper maps with strict reflexivity
and transitivity.

For a finite set `s` of component indices, the intersection of the component members lies in
the inverse image of the intersection of the target members with labels in `s`, and this
inclusion is injective on path components. The target-side criterion
`intersectionsPathSubsingleton_of_preimage` follows from this injectivity, and the same lemma
detects distinct or equal path components inside one target preimage.

No geometric realization, homology, Nerve Lemma, contiguity, selector-independence,
interleaving, approximation or stability statement is proved here.
-/

namespace TDA.Mapper

open Finset Set
open TDA.Topology TDA.Topology.MultiNerveCell

noncomputable section

universe u v w z p

variable {X : Type u} {Y : Type v} {I : Type w} {J : Type z}
  [TopologicalSpace X] [TopologicalSpace Y]

local instance multiNerveRefinementDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-! ## Intersections inside target preimages -/

section preimage

variable (f : C(X, Y)) (U : I → Set Y) (s : Finset (ComponentIndex f U))

/-- An intersection of component members lies in the inverse image of the intersection of the
target members with the labels of `s`.
@isnad1 id=le.0h6v.s8.94474652365f from=translated src=- shape=b7c6fa1d vocab=fce7e102
-/
theorem componentCover_interMember_subset_preimage :
    interMember (componentCover f U) s ⊆ f ⁻¹' ⋂ i ∈ s.image Sigma.fst, U i := by
  intro x hx
  rw [Set.mem_preimage, Set.mem_iInter₂]
  intro i hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
  exact ((mem_interMember_iff _).1 hx a ha).1

/-- The map on path components induced by
`interMember (componentCover f U) s ⊆ f ⁻¹' ⋂ i ∈ s.image Sigma.fst, U i`.-/
def interMemberPreimageMap :
    ZerothHomotopy (interMember (componentCover f U) s) →
      ZerothHomotopy (f ⁻¹' ⋂ i ∈ s.image Sigma.fst, U i) :=
  componentMap (preimageSetInclusion (ContinuousMap.id X)
    (componentCover_interMember_subset_preimage f U s))

/-- Two points of an intersection of component members that are joined inside the inverse
image of the intersection of the target members are joined inside the intersection of the
component members. In particular `intersectionsPathSubsingleton_of_preimage` follows from this
injectivity. No nonemptiness of `s` is needed.
@isnad1 id=injectiv.0h6v.s9.02b6d8f2e27e from=translated src=- shape=5a0817d1 vocab=1b5bb4cc
-/
theorem interMemberPreimageMap_injective :
    Function.Injective (interMemberPreimageMap f U s) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective d
  set P : Set X := f ⁻¹' ⋂ i ∈ s.image Sigma.fst, U i with hPdef
  have hxP : x.1 ∈ P := componentCover_interMember_subset_preimage f U s x.2
  have hyP : y.1 ∈ P := componentCover_interMember_subset_preimage f U s y.2
  have hcd' : (ZerothHomotopy.mk ⟨x.1, hxP⟩ : ZerothHomotopy P) =
      ZerothHomotopy.mk ⟨y.1, hyP⟩ := hcd
  have hxy : JoinedIn P x.1 y.1 := (joinedIn_iff_joined hxP hyP).2 (Quotient.exact hcd')
  let C := pathComponentIn P x.1
  have hC : IsPathConnected C := isPathConnected_pathComponentIn hxP
  have hCP : C ⊆ P := pathComponentIn_subset
  have hxC : x.1 ∈ C := mem_pathComponentIn_self hxP
  have hCsub : C ⊆ interMember (componentCover f U) s := by
    intro z hz
    rw [mem_interMember_iff]
    intro a ha
    have hτa : a.1 ∈ s.image Sigma.fst := Finset.mem_image_of_mem _ ha
    have hPU : P ⊆ f ⁻¹' U a.1 := fun w hw => mem_iInter₂.1 hw a.1 hτa
    have hzU : f z ∈ U a.1 := hPU (hCP hz)
    obtain ⟨hxU, hxc⟩ := (mem_interMember_iff _).1 x.2 a ha
    have hxz : JoinedIn (f ⁻¹' U a.1) x.1 z :=
      (hC.joinedIn _ hxC _ hz).mono (hCP.trans hPU)
    exact ⟨hzU, (mk_eq_of_joinedIn f (U a.1) hxz hxU hzU).symm.trans hxc⟩
  exact ZerothHomotopy.sound ((hC.joinedIn _ hxC _ hxy).mono hCsub).joined_subtype.somePath

end preimage

/-! ## MultiNerve Mapper maps -/

/-- The MultiNerve Mapper map induced by a selected refinement of target families.-/
def multiNerveMapperMap (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y} (R : Refinement U V) :
    multiNerveMapper f U → multiNerveMapper f V :=
  multiNerveMap (componentRefinement f R)

section multiNerveMapperMap

variable (f : C(X, Y))

/--
@isnad1 id=eq.0h9v.s7.85569ed79f93 from=translated src=- shape=5a610218 vocab=8c03d094
-/
@[simp] theorem support_multiNerveMapperMap {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) (c : multiNerveMapper f U) :
    (multiNerveMapperMap f R c).support = c.support.image (componentRefinement f R).selector :=
  rfl

/-- MultiNerve Mapper maps are monotone for the face order.
@isnad1 id=monotone.0h8v.s6.eff5671e0df1 from=translated src=- shape=dca9415d vocab=5d736981
-/
theorem multiNerveMapperMap_monotone {U : I → Set Y} {V : J → Set Y} (R : Refinement U V) :
    Monotone (multiNerveMapperMap f R) :=
  multiNerveMap_monotone (componentRefinement f R)

/-- The identity refinement induces the identity MultiNerve Mapper map.
@isnad1 id=eq.0h5v.s6.b50c211b1f77 from=translated src=- shape=c708c6ed vocab=ed732029
-/
theorem multiNerveMapperMap_id (U : I → Set Y) :
    multiNerveMapperMap f (Refinement.id U) = id := by
  unfold multiNerveMapperMap
  rw [componentRefinement_id]
  exact multiNerveMap_id

/-- Composition of refinements induces composition of MultiNerve Mapper maps.
@isnad1 id=eq.0h11v.s7.6d92ed7daff2 from=translated src=- shape=02ef8d1b vocab=e423daf5
-/
theorem multiNerveMapperMap_comp {K : Type*} {U : I → Set Y} {V : J → Set Y} {W : K → Set Y}
    (R : Refinement U V) (S : Refinement V W) :
    multiNerveMapperMap f (Refinement.comp R S) =
      multiNerveMapperMap f S ∘ multiNerveMapperMap f R := by
  unfold multiNerveMapperMap
  rw [componentRefinement_comp]
  exact multiNerveMap_comp _ _

/-- The square with ordinary Mapper: projecting the image cell gives the image of the projected
Mapper face under `mapperMap f R`.
@isnad1 id=eq.0h9v.s8.90664e78b852 from=translated src=- shape=5f0c237d vocab=853b81ae
-/
theorem multiNerveMapper_projection_multiNerveMapperMap {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) (c : multiNerveMapper f U) :
    (multiNerveMapper_projection f V (multiNerveMapperMap f R c)).1 =
      (multiNerveMapper_projection f U c).1.image (mapperMap f R) :=
  projection_multiNerveMap (componentRefinement f R) c

/-- MultiNerve Mapper maps send vertex cells to vertex cells along `mapperMap f R`.
@isnad1 id=eq.0h9v.s7.2556592a29f0 from=translated src=- shape=917971e4 vocab=0e7c2d1f
-/
theorem multiNerveMapperMap_vertexCell {U : I → Set Y} {V : J → Set Y} (R : Refinement U V)
    (a : ComponentIndex f U) :
    multiNerveMapperMap f R (vertexCell f U a) = vertexCell f V (mapperMap f R a) := by
  apply eq_vertexCell_of_support_eq
  rw [support_multiNerveMapperMap, support_vertexCell, Finset.image_singleton]
  rfl

end multiNerveMapperMap

/-! ## Coherent towers -/

namespace CoherentCoverTower

variable {P : Type p} [Preorder P] (T : CoherentCoverTower Y P)

/-- The MultiNerve Mapper map attached to a comparison in a coherent cover tower.-/
def multiNerveMapperMap (f : C(X, Y)) {q r : P} (h : q ≤ r) :
    multiNerveMapper f (T.cover q) → multiNerveMapper f (T.cover r) :=
  TDA.Mapper.multiNerveMapperMap f (T.refinement h)

/-- A coherent cover tower induces the identity MultiNerve Mapper map on reflexive
comparisons.
@isnad1 id=eq.0h6v.s6.b83f96464d1d from=translated src=- shape=cc8be6e3 vocab=e1a20e46
-/
theorem multiNerveMapperMap_refl (f : C(X, Y)) (q : P) :
    T.multiNerveMapperMap f (le_refl q) = id := by
  have hrefinement : T.refinement (q := q) (r := q) (le_refl q) =
      Refinement.id (T.cover q) := by
    apply Refinement.ext
    intro i
    exact congrFun (T.selector_refl q) i
  unfold multiNerveMapperMap
  rw [hrefinement]
  exact TDA.Mapper.multiNerveMapperMap_id f (T.cover q)

/-- MultiNerve Mapper maps of a coherent cover tower compose strictly.
@isnad1 id=eq.2h8v.s7.f1692c77ffd7 from=translated src=- shape=7bab7be4 vocab=0ad6d958
-/
theorem multiNerveMapperMap_trans (f : C(X, Y)) {q r t : P} (h : q ≤ r) (k : r ≤ t) :
    T.multiNerveMapperMap f k ∘ T.multiNerveMapperMap f h =
      T.multiNerveMapperMap f (h.trans k) := by
  have hrefinement : Refinement.comp (T.refinement h) (T.refinement k) =
      T.refinement (h.trans k) := by
    apply Refinement.ext
    intro i
    exact congrFun (T.selector_trans h k) i
  unfold multiNerveMapperMap
  rw [← TDA.Mapper.multiNerveMapperMap_comp, hrefinement]

end CoherentCoverTower

end

end TDA.Mapper
