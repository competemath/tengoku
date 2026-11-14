import Tengoku.TdaLib.TDA.Mapper.PullbackCoverExamples
import Tengoku.TdaLib.TDA.Mapper.Refinement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordinary Mapper fixtures

These examples exercise the `mapper` definition: disconnected fibers,
duplicate labels, a genuine triangle, a component-merging refinement, and the
multiplicity-two one-skeleton theorem at empty and isolated complexes.
-/

namespace TDA.Mapper.Examples

open Finset Set

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-! ## Two isolated vertices from a disconnected fiber -/

/-- The supported Mapper vertex represented by a Boolean point.-/
def boolMapperVertex (b : Bool) : MapperVertex boolToUnit unitCover :=
  toMapperVertex boolToUnit unitCover (boolComponentIndex b)

/-- The one-member constant-filter Mapper has exactly the two displayed
vertices and no adjacency: the two points lie in distinct path components of
the same pullback member.
@isnad1 id=and.0h0v.s6.14793041d848 from=translated src=- shape=e5f2d175 vocab=179f9756
-/
theorem bool_mapper_two_isolated_vertices :
    boolMapperVertex false ≠ boolMapperVertex true ∧
      (∀ v : MapperVertex boolToUnit unitCover,
        v = boolMapperVertex false ∨ v = boolMapperVertex true) ∧
      ∀ a b : MapperVertex boolToUnit unitCover,
        ¬(mapperOneSkeleton boolToUnit unitCover).Adj a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact bool_component_indices_ne (congrArg Subtype.val h)
  · intro v
    rcases bool_component_indices_exhaustive v.1 with hv | hv
    · exact Or.inl (Subtype.ext hv)
    · exact Or.inr (Subtype.ext hv)
  · intro a b hab
    have hval : a.1 = b.1 :=
      eq_of_mem_mapper_face_of_fst_eq boolToUnit unitCover hab.2
        (by simp) (by simp) (Subsingleton.elim _ _)
    exact hab.1 (Subtype.ext hval)

/-! ## Duplicate labels and an edge -/

/-- A supported Mapper vertex at duplicate cover label `i`, represented by `b`.-/
def duplicateMapperVertex (i b : Bool) : MapperVertex boolToUnit duplicateUnitCover :=
  toMapperVertex boolToUnit duplicateUnitCover (duplicateComponentIndex i b)

/-- Duplicate overlapping members retain distinct labels and give an edge
when their represented component members share a point.
@isnad1 id=and.0h0v.s5.ed9d6c46a330 from=translated src=- shape=3bf97639 vocab=6c84a839
-/
theorem duplicate_labels_give_distinct_adjacent_vertices :
    duplicateMapperVertex false false ≠ duplicateMapperVertex true false ∧
      (mapperOneSkeleton boolToUnit duplicateUnitCover).Adj
        (duplicateMapperVertex false false) (duplicateMapperVertex true false) := by
  constructor
  · intro h
    exact duplicate_labels_remain_distinct (congrArg Subtype.val h)
  · refine ⟨?_, ?_⟩
    · intro h
      exact duplicate_labels_remain_distinct (congrArg Subtype.val h)
    · apply (mem_mapper_iff boolToUnit duplicateUnitCover _).2
      refine ⟨by simp, false, ?_⟩
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · change false ∈ componentCover boolToUnit duplicateUnitCover
          (duplicateComponentIndex false false)
        rw [duplicate_component_member]
        simp
      · change false ∈ componentCover boolToUnit duplicateUnitCover
          (duplicateComponentIndex true false)
        rw [duplicate_component_member]
        simp

/-! ## A genuine triangle -/

/-- The constant map from a one-point domain to a one-point target.-/
def triangleMap : C(Unit, Unit) := ContinuousMap.const Unit ()

/-- Three distinct target labels for the same full target member.-/
def tripleUnitCover : Fin 3 → Set Unit := fun _ => Set.univ

/-- The component-cover index at one of the three duplicate labels.-/
def triangleComponentIndex (i : Fin 3) : ComponentIndex triangleMap tripleUnitCover :=
  ⟨i, ZerothHomotopy.mk ⟨(), Set.mem_univ ()⟩⟩

private theorem triangleComponentIndex_injective :
    Function.Injective triangleComponentIndex := by
  intro i j h
  exact congrArg Sigma.fst h

/-- Three duplicate target labels over a one-point domain form a genuine
three-vertex face, so ordinary Mapper is not globally truncated to a graph.
@isnad1 id=and.0h0v.s9.baa6ec24f22f from=translated src=- shape=0d3d985f vocab=635bb23e
-/
theorem triple_duplicate_cover_has_triangle :
    ({triangleComponentIndex 0, triangleComponentIndex 1, triangleComponentIndex 2} :
        Finset (ComponentIndex triangleMap tripleUnitCover)) ∈
      mapper triangleMap tripleUnitCover ∧
    ({triangleComponentIndex 0, triangleComponentIndex 1, triangleComponentIndex 2} :
        Finset (ComponentIndex triangleMap tripleUnitCover)).card = 3 := by
  constructor
  · apply (mem_mapper_iff triangleMap tripleUnitCover _).2
    refine ⟨⟨triangleComponentIndex 0, Finset.mem_insert_self _ _⟩, (), ?_⟩
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> exact ⟨Set.mem_univ (), rfl⟩
  · have h01 : triangleComponentIndex 0 ≠ triangleComponentIndex 1 :=
      triangleComponentIndex_injective.ne (by decide)
    have h02 : triangleComponentIndex 0 ≠ triangleComponentIndex 2 :=
      triangleComponentIndex_injective.ne (by decide)
    have h12 : triangleComponentIndex 1 ≠ triangleComponentIndex 2 :=
      triangleComponentIndex_injective.ne (by decide)
    simp [h01, h02, h12]

/-! ## A noninjective Mapper refinement map -/

/-- The supported Mapper vertex of the left source interval component.-/
def leftIntervalMapperVertex : MapperVertex realMap twoIntervalCover :=
  toMapperVertex realMap twoIntervalCover
    ⟨(), ZerothHomotopy.mk leftSourcePoint⟩

/-- The supported Mapper vertex of the right source interval component.-/
def rightIntervalMapperVertex : MapperVertex realMap twoIntervalCover :=
  toMapperVertex realMap twoIntervalCover
    ⟨(), ZerothHomotopy.mk rightSourcePoint⟩

/-- The proper interval refinement merges two distinct source Mapper vertices.
@isnad1 id=and.0h0v.s9.3ce441204485 from=translated src=- shape=91bbdfe2 vocab=a7511231
-/
theorem interval_mapper_refinement_is_noninjective :
    leftIntervalMapperVertex ≠ rightIntervalMapperVertex ∧
      mapperMap realMap intervalRefinement leftIntervalMapperVertex.1 =
        mapperMap realMap intervalRefinement rightIntervalMapperVertex.1 := by
  constructor
  · intro h
    exact source_interval_indices_ne (congrArg Subtype.val h)
  · exact interval_componentRefinement_merges

/-! ## Empty and isolated multiplicity-two specializations -/

/-- The empty-domain fixture satisfies every target-cover multiplicity bound.
@isnad1 id=covermul.0h0v.s3.704f1a4359bc from=translated src=- shape=690219a0 vocab=c4c4bbb4
-/
theorem emptyDomain_multiplicity_two :
    CoverMultiplicityAtMost emptyDomainMap unitCover 2 := by
  intro y hy
  obtain ⟨x, _⟩ := hy
  exact isEmptyElim x

/-- The empty-domain Mapper is the bottom preabstract complex.
@isnad1 id=eq.0h0v.s5.5a9b6201f6f8 from=translated src=- shape=0f4dd44f vocab=d12ac9ad
-/
theorem emptyDomain_mapper_eq_bot :
    mapper emptyDomainMap unitCover =
      (⊥ : PreAbstractSimplicialComplex (ComponentIndex emptyDomainMap unitCover)) := by
  unfold mapper
  exact TDA.Topology.nerve_eq_bot_of_isEmpty (componentCover emptyDomainMap unitCover)

/-- The multiplicity-two graph characterization specializes without an
inhabitedness assumption to the empty Mapper.
@isnad1 id=iff.0h1v.s9.81fc47d406b8 from=translated src=- shape=7938e272 vocab=fe9252bd
-/
theorem emptyDomain_mapper_graph_characterization
    (s : Finset (ComponentIndex emptyDomainMap unitCover)) :
    s ∈ mapper emptyDomainMap unitCover ↔
      (∃ a : MapperVertex emptyDomainMap unitCover, s = {a.1}) ∨
        ∃ a b : MapperVertex emptyDomainMap unitCover,
          (mapperOneSkeleton emptyDomainMap unitCover).Adj a b ∧
            s = {a.1, b.1} :=
  mem_mapper_iff_supported_singleton_or_adjacent_pair
    emptyDomainMap unitCover emptyDomain_multiplicity_two s

/-- A one-member cover has multiplicity at most two on the constant Boolean
filter's attained range.
@isnad1 id=covermul.0h0v.s3.5ec6c9da6e98 from=translated src=- shape=690219a0 vocab=102374b2
-/
theorem bool_multiplicity_two : CoverMultiplicityAtMost boolToUnit unitCover 2 := by
  intro _ _ t _
  exact (Finset.card_le_one_of_subsingleton t).trans (by omega)

/-- The multiplicity-two graph characterization includes the isolated
vertices of the disconnected Boolean fiber.
@isnad1 id=iff.0h1v.s9.199491b678be from=translated src=- shape=7938e272 vocab=c217a900
-/
theorem bool_mapper_graph_characterization
    (s : Finset (ComponentIndex boolToUnit unitCover)) :
    s ∈ mapper boolToUnit unitCover ↔
      (∃ a : MapperVertex boolToUnit unitCover, s = {a.1}) ∨
        ∃ a b : MapperVertex boolToUnit unitCover,
          (mapperOneSkeleton boolToUnit unitCover).Adj a b ∧
            s = {a.1, b.1} :=
  mem_mapper_iff_supported_singleton_or_adjacent_pair
    boolToUnit unitCover bool_multiplicity_two s

end

end TDA.Mapper.Examples
