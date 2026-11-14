import Tengoku.TdaLib.TDA.Topology.Nerve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete ordinary-nerve fixtures

These declarations exercise support-sensitive vertices, duplicate labels,
pairwise-but-not-triple intersections, strict pullback loss, and empty types.
-/

namespace TDA.Topology.NerveExamples

/-- A family with an inhabited index type but an empty member.-/
def emptyMemberFamily : CoverFamily Bool (Fin 1) := fun _ => ∅

/-- An empty member does not create a vertex.
@isnad1 id=not.0h0v.s6.5ebc51d41ff1 from=translated src=- shape=24c6ed03 vocab=761f0176
-/
theorem emptyMember_has_no_vertex :
    ¬ ({0} : Finset (Fin 1)) ∈ nerve emptyMemberFamily := by
  simp [mem_nerve_iff, emptyMemberFamily]

/-- Two distinct labels carry the same nonempty member.-/
def duplicateFamily : CoverFamily Bool (Fin 2) := fun _ => {true}

/-- Both duplicate labels are vertices of the nerve.
@isnad1 id=and.0h0v.s7.70309c58c2ad from=translated src=- shape=da7895f1 vocab=576ca343
-/
theorem duplicateFamily_has_two_vertices :
    ({0} : Finset (Fin 2)) ∈ nerve duplicateFamily ∧
      ({1} : Finset (Fin 2)) ∈ nerve duplicateFamily := by
  simp [mem_nerve_iff, duplicateFamily]

/-- The two duplicate vertices span an edge.
@isnad1 id=mem.0h0v.s6.6790080e55a6 from=translated src=- shape=b9faf450 vocab=4cc124b5
-/
theorem duplicateFamily_has_edge :
    ({0, 1} : Finset (Fin 2)) ∈ nerve duplicateFamily := by
  simp [mem_nerve_iff, duplicateFamily]

/-- Three members have all pairwise intersections but no common triple point.-/
def pairwiseFamily : CoverFamily (Fin 3) (Fin 3) := fun i =>
  if i = 0 then {0, 1} else if i = 1 then {1, 2} else {0, 2}

/-- Every edge in the pairwise fixture is a face.
@isnad1 id=and.0h0v.s8.8c8e31c50c48 from=translated src=- shape=f6b0a56a vocab=6a28e23e
-/
theorem pairwiseFamily_has_all_edges :
    ({0, 1} : Finset (Fin 3)) ∈ nerve pairwiseFamily ∧
      ({0, 2} : Finset (Fin 3)) ∈ nerve pairwiseFamily ∧
      ({1, 2} : Finset (Fin 3)) ∈ nerve pairwiseFamily := by
  simp [mem_nerve_iff, pairwiseFamily]

/-- Two disjoint target members, retained as two labelled vertices.-/
def disjointFamily : CoverFamily Bool (Fin 2) := fun i =>
  if i = 0 then {false} else {true}

/-- A constant map lands in the first target member.-/
def constantMap : Fin 1 → Bool := fun _ => false

/-- The target nerve has both disjoint-family vertices.
@isnad1 id=and.0h0v.s7.cf560514a4c1 from=translated src=- shape=da7895f1 vocab=b3ff31af
-/
theorem disjointFamily_has_target_vertices :
    ({0} : Finset (Fin 2)) ∈ nerve disjointFamily ∧
      ({1} : Finset (Fin 2)) ∈ nerve disjointFamily := by
  simp [mem_nerve_iff, disjointFamily]

/-- The constant pullback retains the first target vertex.
@isnad1 id=mem.0h0v.s6.05d9e947556b from=translated src=- shape=77a2ea2e vocab=b656fe9a
-/
theorem constantPullback_has_first_vertex :
    ({0} : Finset (Fin 2)) ∈ nerve (pullback constantMap disjointFamily) := by
  simp [mem_nerve_iff, pullback, disjointFamily, constantMap]

/-- The constant pullback loses the second target vertex.
@isnad1 id=not.0h0v.s6.81e99d2fa011 from=translated src=- shape=40666678 vocab=b656fe9a
-/
theorem constantPullback_has_no_second_vertex :
    ¬ ({1} : Finset (Fin 2)) ∈ nerve (pullback constantMap disjointFamily) := by
  simp [mem_nerve_iff, pullback, disjointFamily, constantMap]

/-- The constant pullback is a proper subcomplex of the disjoint target nerve.
@isnad1 id=lt.0h0v.s5.42b7f14d2c7e from=translated src=- shape=f4441322 vocab=53d2c97d
-/
theorem constantPullback_is_proper_subcomplex :
    nerve (pullback constantMap disjointFamily) < nerve disjointFamily := by
  refine ⟨nerve_pullback_le constantMap disjointFamily, ?_⟩
  intro h
  exact constantPullback_has_no_second_vertex (h disjointFamily_has_target_vertices.2)

/-- An empty ambient type gives the bottom nerve without an inhabitedness assumption.-/
def emptyAmbientFamily : CoverFamily Empty (Fin 1) := fun _ => ∅

/--
@isnad1 id=eq.0h0v.s5.489b2aa6b8fa from=translated src=- shape=ce11c7bd vocab=502baa13
-/
theorem emptyAmbient_nerve_is_bot :
    nerve emptyAmbientFamily = (⊥ : PreAbstractSimplicialComplex (Fin 1)) := by
  exact nerve_eq_bot_of_isEmpty emptyAmbientFamily

/-- An empty index type gives the bottom nerve without an inhabitedness assumption.-/
def emptyIndexFamily : CoverFamily Bool Empty := Empty.elim

/--
@isnad1 id=eq.0h0v.s3.4348c8d32ecc from=translated src=- shape=1a72b0cd vocab=5b90996e
-/
theorem emptyIndex_nerve_is_bot :
    nerve emptyIndexFamily = (⊥ : PreAbstractSimplicialComplex Empty) := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  constructor
  · intro hs
    obtain ⟨i, _⟩ := (mem_nerve_iff emptyIndexFamily s).1 hs |>.1
    exact Empty.elim i
  · intro hs
    exact hs.elim

end TDA.Topology.NerveExamples
