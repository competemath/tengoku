/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Defs

/-!
# Counting endpoint marks and lost degrees

A cut edge has exactly one outside endpoint, so its contribution has total
one. On a set avoiding the region, its marks count exactly those boundary
edges crossing the set. For disjoint regions, marks on an outside vertex
are precisely its incident deleted edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V) (P : Finset V)

omit [Fintype V] in
private theorem outside_endpoints {a b : V} (ha : a ∈ P) (hb : b ∉ P) :
    s(a, b).toFinset \ P = {b} := by
  ext v
  simp only [Finset.mem_sdiff, Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hv⟩
    · exact (hv ha).elim
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, hb⟩

/--
@isnad1 id=eq.0h3v.s7.fe4bf19c5fb7 from=translated src=- shape=21cd58e5 vocab=22a9d6e8
-/
theorem degree_boundaryMarks : (boundaryMarks B P).degree = (B.cutFinset P).card := by
  simp only [boundaryMarks, map_sum, Finsupp.degree_single, Finset.sum_const,
    nsmul_eq_mul, Nat.mul_one]
  calc
    (∑ e ∈ B.cutFinset P, (e.toFinset \ P).card) = ∑ _e ∈ B.cutFinset P, 1 := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨_, a, b, rfl, ha, hb⟩ := B.mem_cutFinset.mp he
      rw [outside_endpoints P ha hb]
      simp
    _ = _ := by simp

/--
@isnad1 id=eq.1h4v.s6.86f1e91e419c from=translated src=- shape=aeeebc21 vocab=287342e2
-/
theorem sum_boundaryMarks {X : Finset V} (fresh : Disjoint X P) :
    (∑ v ∈ X, boundaryMarks B P v) = (B.cutFinset P ∩ B.cutFinset X).card := by
  simp only [boundaryMarks, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  have each (e : Sym2 V) (he : e ∈ B.cutFinset P) :
      (∑ v ∈ X, ∑ w ∈ e.toFinset \ P, (Finsupp.single w 1 : V →₀ ℕ) v) =
        if e ∈ B.cutFinset X then 1 else 0 := by
    obtain ⟨edge, a, b, rfl, ha, hb⟩ := B.mem_cutFinset.mp he
    have outsideA : a ∉ X := fun h => Finset.disjoint_left.mp fresh h ha
    have adjacent := B.mem_edgeSet.mp edge
    rw [outside_endpoints P ha hb]
    simp [Finsupp.single_apply, B.mem_cutFinset_mk, adjacent, outsideA]
  calc
    _ = ∑ e ∈ B.cutFinset P, if e ∈ B.cutFinset X then 1 else 0 :=
      Finset.sum_congr rfl each
    _ = _ := by simp

variable {E ι : Type} [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι)

/--
@isnad1 id=eq.0h6v.s7.a5422f34cd02 from=translated src=- shape=df3ae7f0 vocab=cb73990d
-/
theorem degree_endpointMarks : F.endpointMarks.degree = ∑ i, (B.cutFinset (F.region i)).card := by
  simp only [endpointMarks, map_sum, degree_boundaryMarks]

/--
@isnad1 id=eq.1h7v.s7.50f92d0e96e8 from=translated src=- shape=c4cabba4 vocab=00a9434b
-/
theorem sum_endpointMarks {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    (∑ v ∈ X, F.endpointMarks v) = ∑ i, (B.cutFinset (F.region i) ∩ B.cutFinset X).card := by
  simp only [endpointMarks, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => sum_boundaryMarks B (F.region i) (fresh i))

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal
