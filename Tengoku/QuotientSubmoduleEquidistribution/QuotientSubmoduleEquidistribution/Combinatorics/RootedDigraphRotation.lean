import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Combinatorics.RootedDigraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rotation of grouped top-part data

This file isolates the precise graph-theoretic content of AR mesh rotation.
The rotation is an anti-isomorphism on nonboundary vertices and identifies
incoming arrows at a source support with incoming arrows at its rotated
target support without relabeling the other endpoint.  These two clauses are
exactly what is used in the rooted-balance inclusion--exclusion argument.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RootedDigraph

universe u

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

/-- The graph-theoretic mesh-rotation interface behind rooted balance.-/
structure GroupedRotationData
    (qEdge sEdge : Vertex → Vertex → Prop)
    (P I : Finset Vertex) where
  perm : Equiv.Perm Vertex
  nonboundary_iff : ∀ x, x ∉ P ↔ perm x ∉ I
  edge_iff : ∀ {x y}, x ∉ P → y ∉ P →
    (qEdge x y ↔ sEdge (perm y) (perm x))
  incoming_iff : ∀ {x y}, y ∉ P →
    (qEdge x y ↔ sEdge x (perm y))

namespace GroupedRotationData

variable {qEdge sEdge : Vertex → Vertex → Prop}
  {P I : Finset Vertex}
  (R : GroupedRotationData qEdge sEdge P I)

/-- Reverse a grouped rotation.-/
def symm : GroupedRotationData sEdge qEdge I P where
  perm := R.perm.symm
  nonboundary_iff := by
    intro x
    simpa using (R.nonboundary_iff (R.perm.symm x)).symm
  edge_iff := by
    intro x y hx hy
    have hx' : R.perm.symm x ∉ P :=
      (R.nonboundary_iff (R.perm.symm x)).2 (by simpa using hx)
    have hy' : R.perm.symm y ∉ P :=
      (R.nonboundary_iff (R.perm.symm y)).2 (by simpa using hy)
    simpa using
      (R.edge_iff hy' hx').symm
  incoming_iff := by
    intro x y hy
    have hy' : R.perm.symm y ∉ P :=
      (R.nonboundary_iff (R.perm.symm y)).2 (by simpa using hy)
    simpa using
      (R.incoming_iff (x := x) hy').symm

/-- In a separated family of strongly connected supports, a vertex has an
internal outgoing edge exactly when it has an internal incoming edge.-/
theorem exists_outgoing_iff_exists_incoming_supportFamilyUnion
    {C : Finset (Finset Vertex)}
    (hCandidates : ∀ S ∈ C,
      S ∈ minimalTopPartCandidates qEdge P)
    (hSeparated : IsSeparatedSupportFamily qEdge C)
    {x : Vertex} (hx : x ∈ supportFamilyUnion C) :
    (∃ y ∈ supportFamilyUnion C, qEdge x y) ↔
      ∃ y ∈ supportFamilyUnion C, qEdge y x := by
  obtain ⟨S, hSC, hxS⟩ := Finset.mem_biUnion.mp hx
  have hSstrong :=
    (mem_minimalTopPartCandidates.mp (hCandidates S hSC)).2
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨T, hTC, hyT⟩ := Finset.mem_biUnion.mp hy
    have hST : S = T := by
      by_contra hne
      exact hSeparated.2 S hSC T hTC hne x hxS y hyT hxy
    subst T
    rcases Relation.ReflTransGen.cases_tail
        (hSstrong y hyT x hxS) with h | ⟨z, hyz, hzx⟩
    · subst y
      exact ⟨x, hx, hxy⟩
    · exact
        ⟨z,
          Finset.mem_biUnion.mpr ⟨S, hSC, hzx.1⟩,
          hzx.2.2⟩
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨T, hTC, hyT⟩ := Finset.mem_biUnion.mp hy
    have hST : S = T := by
      by_contra hne
      exact hSeparated.2 T hTC S hSC (Ne.symm hne) y hyT x hxS hyx
    subst T
    rcases Relation.ReflTransGen.cases_head
        (hSstrong x hxS y hyT) with h | ⟨z, hxz, hzy⟩
    · subst y
      exact ⟨x, hx, hyx⟩
    · exact
        ⟨z,
          Finset.mem_biUnion.mpr ⟨S, hSC, hxz.2.1⟩,
          hxz.2.2⟩

end GroupedRotationData

end QuotientSubmoduleEquidistribution.RootedDigraph
