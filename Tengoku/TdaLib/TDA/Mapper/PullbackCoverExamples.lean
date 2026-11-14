import Tengoku.TdaLib.TDA.Mapper.PullbackCover
import Tengoku.TdaLib.TDA.Reeb.ComponentsDiscrete
import Tengoku.Seed.Analysis.Convex.PathConnected
import Tengoku.Seed.Topology.Order.IntermediateValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path-component pullback-cover fixtures

Concrete regression fixtures for empty and duplicate indices, disconnected discrete fibers,
and a refinement that merges two real path components.
-/

namespace TDA.Mapper.Examples

noncomputable section

open Set

/-! ## Empty fibers -/

/-- The unique covered target point receives the empty inverse image from an empty domain.-/
def emptyDomainMap : C(Empty, Unit) := ContinuousMap.const Empty ()

/-- A one-member full cover of `Unit`.-/
def unitCover : Unit → Set Unit := fun _ => Set.univ

/-- An empty domain produces no component-cover index.
@isnad1 id=isempty.0h0v.s3.d827c96694a2 from=translated src=- shape=c09797fa vocab=74904d8c
-/
theorem emptyDomain_componentIndex_isEmpty :
    IsEmpty (ComponentIndex emptyDomainMap unitCover) :=
  ⟨fun a => by
    rcases a with ⟨i, c⟩
    have h : IsEmpty (PullbackSpace emptyDomainMap unitCover i) :=
      ⟨fun x => isEmptyElim x.1⟩
    exact (componentType_isEmpty emptyDomainMap unitCover i h).false c⟩

/-- A one-member family whose sole member is empty.-/
def emptyMemberFamily : Unit → Set Unit := fun _ => ∅

/-- An empty pullback member contributes no component-cover index.
@isnad1 id=not.0h0v.s6.452116852a47 from=translated src=- shape=9450f47a vocab=648ee6b7
-/
theorem emptyMember_no_component_index :
    ¬ ∃ a : ComponentIndex (ContinuousMap.id Unit) emptyMemberFamily, a.1 = () :=
  no_componentIndex_of_isEmpty (ContinuousMap.id Unit) emptyMemberFamily ()
    ⟨fun x => x.2⟩

/-! ## Discrete two-point fibers and duplicate labels -/

/-- The constant map from discrete `Bool` to the covered point.-/
def boolToUnit : C(Bool, Unit) := ContinuousMap.const Bool ()

/-- A point of the full inverse-image subspace.-/
def boolPoint (b : Bool) : PullbackSpace boolToUnit unitCover () := ⟨b, Set.mem_univ ()⟩

/-- The component-cover index represented by `b`.-/
def boolComponentIndex (b : Bool) : ComponentIndex boolToUnit unitCover :=
  ⟨(), ZerothHomotopy.mk (boolPoint b)⟩

/-- In the discrete two-point fiber, the component member represented by `b` is `{b}`.
@isnad1 id=eq.0h1v.s4.31aa74f314c5 from=translated src=- shape=1dc7f4d5 vocab=9ddbd4fa
-/
theorem bool_component_member (b : Bool) :
    componentCover boolToUnit unitCover (boolComponentIndex b) = {b} := by
  ext x
  constructor
  · rintro ⟨hx, hclass⟩
    change x = b
    exact congrArg Subtype.val (TDA.Reeb.joined_eq_of_discrete (Quotient.exact hclass))
  · intro hxb
    change x = b at hxb
    subst x
    exact ⟨Set.mem_univ (), rfl⟩

/-- The two discrete component classes are distinct.
@isnad1 id=ne.0h0v.s6.cc97d3cef152 from=translated src=- shape=9a2d1609 vocab=e19627bf
-/
theorem bool_component_classes_ne :
    ZerothHomotopy.mk (boolPoint false) ≠ ZerothHomotopy.mk (boolPoint true) := by
  intro h
  exact Bool.false_ne_true
    (congrArg Subtype.val (TDA.Reeb.joined_eq_of_discrete (Quotient.exact h)))

/-- The constant map from discrete `Bool` into one covered point has two distinct component
members.
@isnad1 id=ne.0h0v.s3.4aabaf0351ef from=translated src=- shape=09a7fa84 vocab=d5aa7e12
-/
theorem bool_component_indices_ne : boolComponentIndex false ≠ boolComponentIndex true := by
  intro h
  have hsnd : ZerothHomotopy.mk (boolPoint false) = ZerothHomotopy.mk (boolPoint true) :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  exact bool_component_classes_ne hsnd

/-- The two displayed component indices exhaust the component cover of the discrete fiber.
@isnad1 id=or.0h1v.s5.ec2ec92abbad from=translated src=- shape=4260cfa2 vocab=d5aa7e12
-/
theorem bool_component_indices_exhaustive (a : ComponentIndex boolToUnit unitCover) :
    a = boolComponentIndex false ∨ a = boolComponentIndex true := by
  rcases a with ⟨i, c⟩
  rcases i with ⟨⟩
  induction c using ZerothHomotopy.rec with
  | mk x =>
      rcases x with ⟨b, hb⟩
      cases b with
      | false =>
          left
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact congrArg ZerothHomotopy.mk (Subtype.ext rfl)
      | true =>
          right
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact congrArg ZerothHomotopy.mk (Subtype.ext rfl)

/-- Two duplicate target labels, each covering the same point.-/
def duplicateUnitCover : Bool → Set Unit := fun _ => Set.univ

/-- The copy, at label `i`, of the component represented by `b`.-/
def duplicateComponentIndex (i b : Bool) : ComponentIndex boolToUnit duplicateUnitCover :=
  ⟨i, ZerothHomotopy.mk ⟨b, Set.mem_univ ()⟩⟩

/-- Duplicate labels give equal underlying component members.
@isnad1 id=eq.0h2v.s4.dc3026a9618d from=translated src=- shape=16854eef vocab=79a4873c
-/
theorem duplicate_component_member (i b : Bool) :
    componentCover boolToUnit duplicateUnitCover (duplicateComponentIndex i b) = {b} := by
  ext x
  constructor
  · rintro ⟨hx, hclass⟩
    change x = b
    exact congrArg Subtype.val (TDA.Reeb.joined_eq_of_discrete (Quotient.exact hclass))
  · intro hxb
    change x = b at hxb
    subst x
    exact ⟨Set.mem_univ (), rfl⟩

/-- Duplicate original labels remain distinct copies in the component-cover index.
@isnad1 id=ne.0h0v.s3.f3578ed6e1de from=translated src=- shape=ac64b45a vocab=3bacc226
-/
theorem duplicate_labels_remain_distinct :
    duplicateComponentIndex false false ≠ duplicateComponentIndex true false :=
  componentIndex_ne_of_index_ne boolToUnit duplicateUnitCover Bool.false_ne_true _ _

/-! ## A refinement that merges two real components -/

/-- The identity map on the real line.-/
def realMap : C(ℝ, ℝ) := ContinuousMap.id ℝ

/-- Two disjoint source intervals.-/
def twoIntervalCover : Unit → Set ℝ :=
  fun _ => Set.Ioo (-2) (-1) ∪ Set.Ioo 1 2

/-- A target interval containing both source intervals and the gap between them.-/
def middleIntervalCover : Unit → Set ℝ :=
  fun _ => Set.Ioo (-3) 3

/-- A still wider interval, used for the nonidentity composition fixture.-/
def wideIntervalCover : Unit → Set ℝ :=
  fun _ => Set.Ioo (-4) 4

/-- The selected proper inclusion from the two source intervals into the middle interval.-/
def intervalRefinement : TDA.Topology.Refinement twoIntervalCover middleIntervalCover where
  selector _ := ()
  subset _ x hx := by
    rcases hx with ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩ <;> constructor <;> linarith

/-- The selected proper inclusion from the middle interval into the wider interval.-/
def wideIntervalRefinement : TDA.Topology.Refinement middleIntervalCover wideIntervalCover where
  selector _ := ()
  subset _ x hx := by
    rcases hx with ⟨hx₁, hx₂⟩
    constructor <;> linarith

/-- The point `-3/2` in the left source interval.-/
def leftSourcePoint : PullbackSpace realMap twoIntervalCover () :=
  ⟨(-3 / 2 : ℝ), by left; constructor <;> norm_num [realMap]⟩

/-- The point `3/2` in the right source interval.-/
def rightSourcePoint : PullbackSpace realMap twoIntervalCover () :=
  ⟨(3 / 2 : ℝ), by right; constructor <;> norm_num [realMap]⟩

/-- The source family is nonempty.
@isnad1 id=nonempty.0h0v.s2.6814fabdff8e from=translated src=- shape=0072ad64 vocab=11af724d
-/
theorem twoIntervalCover_nonempty : (twoIntervalCover ()).Nonempty :=
  ⟨-3 / 2, leftSourcePoint.2⟩

/-- The source member is a proper subset of the selected target member.
@isnad1 id=and.0h0v.s4.5c83c9cf2c91 from=translated src=- shape=81bda1e9 vocab=d4852532
-/
theorem intervalRefinement_proper :
    twoIntervalCover () ⊆ middleIntervalCover () ∧
      twoIntervalCover () ≠ middleIntervalCover () := by
  refine ⟨intervalRefinement.subset (), ?_⟩
  intro h
  have hzero : (0 : ℝ) ∈ twoIntervalCover () := h.symm ▸ (show (0 : ℝ) ∈ middleIntervalCover () by
    constructor <;> norm_num)
  norm_num [twoIntervalCover] at hzero

/-- The classes of `-3/2` and `3/2` are distinct in the disconnected source inverse image.
@isnad1 id=ne.0h0v.s7.67b4e776c3f3 from=translated src=- shape=f2640b38 vocab=1de10a07
-/
theorem source_interval_classes_ne :
    ZerothHomotopy.mk leftSourcePoint ≠ ZerothHomotopy.mk rightSourcePoint := by
  intro h
  obtain ⟨γ⟩ := Quotient.exact h
  let q : Path (-3 / 2 : ℝ) (3 / 2 : ℝ) := γ.map continuous_subtype_val
  have hzero : (0 : ℝ) ∈ Set.range q := by
    apply intermediate_value_univ (0 : unitInterval) (1 : unitInterval) q.continuous
    change q 0 ≤ 0 ∧ 0 ≤ q 1
    rw [q.source, q.target]
    norm_num
  rcases hzero with ⟨t, ht⟩
  have hval : (γ t).1 = (0 : ℝ) := by
    change q t = 0
    exact ht
  have : (0 : ℝ) ∈ twoIntervalCover () := hval ▸ (γ t).2
  norm_num [twoIntervalCover] at this

/-- The corresponding component-cover indices are distinct before refinement.
@isnad1 id=ne.0h0v.s8.9c6305b9904f from=translated src=- shape=4ce163e0 vocab=159a07f4
-/
theorem source_interval_indices_ne :
    (⟨(), ZerothHomotopy.mk leftSourcePoint⟩ : ComponentIndex realMap twoIntervalCover) ≠
      ⟨(), ZerothHomotopy.mk rightSourcePoint⟩ := by
  intro h
  apply source_interval_classes_ne
  exact eq_of_heq (Sigma.ext_iff.mp h).2

/-- The two source classes become equal after transport into the connected target interval.
@isnad1 id=eq.0h0v.s8.5b45f6061d20 from=translated src=- shape=d2c0b7c8 vocab=c51a721c
-/
theorem interval_transport_merges_classes :
    componentRefinementMap realMap intervalRefinement ()
        (ZerothHomotopy.mk leftSourcePoint) =
      componentRefinementMap realMap intervalRefinement ()
        (ZerothHomotopy.mk rightSourcePoint) := by
  change ZerothHomotopy.mk (refinementInclusion realMap intervalRefinement () leftSourcePoint) =
    ZerothHomotopy.mk (refinementInclusion realMap intervalRefinement () rightSourcePoint)
  have hpath : IsPathConnected (Set.Ioo (-3 : ℝ) 3) :=
    (convex_Ioo (-3 : ℝ) 3).isPathConnected ⟨0, by constructor <;> norm_num⟩
  let _ : PathConnectedSpace (PullbackSpace realMap middleIntervalCover ()) :=
    isPathConnected_iff_pathConnectedSpace.mp hpath
  exact ZerothHomotopy.sound (PathConnectedSpace.somePath _ _)

/-- The selected component refinement itself identifies the two displayed source indices.
@isnad1 id=eq.0h0v.s8.3d4d442b018c from=translated src=- shape=a662b701 vocab=46e1f8ea
-/
theorem interval_componentRefinement_merges :
    (componentRefinement realMap intervalRefinement).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      (componentRefinement realMap intervalRefinement).selector
        ⟨(), ZerothHomotopy.mk rightSourcePoint⟩ := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact interval_transport_merges_classes

/-- Representative formula for the nonempty proper interval inclusion.
@isnad1 id=eq.0h0v.s9.d9c14355e996 from=translated src=- shape=c676fbf3 vocab=fb99bb98
-/
theorem interval_refinement_left_representative :
    (componentRefinement realMap intervalRefinement).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      ⟨(), ZerothHomotopy.mk
        (refinementInclusion realMap intervalRefinement () leftSourcePoint)⟩ :=
  componentRefinement_selector_mk realMap intervalRefinement () leftSourcePoint

/-- Identity refinement fixes the represented left source component.
@isnad1 id=eq.0h0v.s8.c25086e1796b from=translated src=- shape=231eb536 vocab=aa36e902
-/
theorem interval_identity_left_representative :
    (componentRefinement realMap (TDA.Topology.Refinement.id twoIntervalCover)).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ := by
  rw [componentRefinement_id]
  rfl

/-- Composition of the two nonidentity interval refinements agrees on the represented left
source component.
@isnad1 id=eq.0h0v.s9.a896fda7d19f from=translated src=- shape=46fe69c8 vocab=06c5b840
-/
theorem interval_composition_left_representative :
    (componentRefinement realMap
        (TDA.Topology.Refinement.comp intervalRefinement wideIntervalRefinement)).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ =
      (TDA.Topology.Refinement.comp
        (componentRefinement realMap intervalRefinement)
        (componentRefinement realMap wideIntervalRefinement)).selector
        ⟨(), ZerothHomotopy.mk leftSourcePoint⟩ := by
  rw [componentRefinement_comp]

end

end TDA.Mapper.Examples
