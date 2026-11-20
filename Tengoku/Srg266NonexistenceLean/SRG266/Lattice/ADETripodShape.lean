/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEPathShape

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

noncomputable def puncturedNeighborComponent (G : SimpleGraph V) (z : V)
    (w : G.neighborSet z) :
    (G.induce {x | x ≠ z}).ConnectedComponent :=
  (G.induce {x | x ≠ z}).connectedComponentMk
    ⟨w.1, w.2.ne'⟩

/--
@isnad1 id=injectiv.1h3v.s5.88e0c941f275 from=translated src=- shape=5f3e9c3d vocab=f9609b79
-/
theorem puncturedNeighborComponent_injective {G : SimpleGraph V} {z : V}
    (hacyc : G.IsAcyclic) :
    Function.Injective (puncturedNeighborComponent G z) := by
  classical
  intro a b hab
  apply Subtype.ext
  by_contra habv
  let S : Set V := {x | x ≠ z}
  let R : SimpleGraph S := G.induce S
  let av : S := ⟨a.1, a.2.ne'⟩
  let bv : S := ⟨b.1, b.2.ne'⟩
  have hcomp : R.connectedComponentMk av = R.connectedComponentMk bv := by
    exact hab
  have hreach : R.Reachable av bv := ConnectedComponent.exact hcomp
  let q : R.Path av bv := hreach.some.toPath
  let incl : R →g G :=
    { toFun := Subtype.val
      map_rel' := fun h ↦ h }
  let qG : G.Walk a.1 b.1 := (q.1.map incl).copy rfl rfl
  have hqG : qG.IsPath := by
    change ((q.1.map incl).copy rfl rfl).IsPath
    rw [Walk.isPath_copy]
    exact q.2.map (f := incl) Subtype.val_injective
  let p0 : G.Walk a.1 a.1 := Walk.nil
  let p1 : G.Walk a.1 z := p0.concat a.2.symm
  let p2 : G.Walk a.1 b.1 := p1.concat b.2
  have hp0 : p0.IsPath := by simp [p0]
  have hp1 : p1.IsPath := by
    apply hp0.concat
    simp [p0, a.2.ne]
  have hp2 : p2.IsPath := by
    apply hp1.concat
    simp only [p1, p0, Walk.support_concat, Walk.support_nil,
      List.mem_append, List.mem_singleton]
    intro hb
    rcases hb with hb | hb
    · exact habv hb.symm
    · exact b.2.ne' hb
  have hpq : qG = p2 :=
    Subtype.mk.inj ((hacyc.subsingleton_path _ _).elim ⟨qG, hqG⟩ ⟨p2, hp2⟩)
  have hzq : z ∉ qG.support := by
    simp only [qG, Walk.support_copy, Walk.support_map, incl, List.mem_map,
      not_exists, not_and]
    intro x _ hx
    exact x.2 hx
  have hzp : z ∈ p2.support := by
    simp [p2, p1, p0]
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  exact hzq (hpq.symm ▸ hzp)

/--
@isnad1 id=surjecti.1h3v.s5.287ba66c585d from=translated src=- shape=5f3e9c3d vocab=da45c0cf
-/
theorem puncturedNeighborComponent_surjective {G : SimpleGraph V} {z : V}
    (hconn : G.Connected) :
    Function.Surjective (puncturedNeighborComponent G z) := by
  classical
  intro C
  let x : {v : V // v ≠ z} := C.out
  have hzx : z ≠ x.1 := Ne.symm x.2
  obtain ⟨p, hp⟩ := hconn.exists_isPath z x.1
  have hp_ne : ¬ p.Nil := Walk.not_nil_of_ne hzx
  have hadj : G.Adj z p.snd := p.adj_snd hp_ne
  let w : G.neighborSet z := ⟨p.snd, hadj⟩
  have htail_mem : ∀ y ∈ p.tail.support, y ≠ z := by
    intro y hy hyz
    subst y
    have hnodup := hp.support_nodup
    rw [← p.cons_support_tail hp_ne] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hy
  let q := p.tail.induce {v : V | v ≠ z} htail_mem
  have hreach : (G.induce {v : V | v ≠ z}).Reachable
      ⟨p.snd, hadj.ne'⟩ x := by
    refine ⟨q.copy ?_ ?_⟩
    · rfl
    · exact Subtype.ext rfl
  refine ⟨w, ?_⟩
  dsimp only [puncturedNeighborComponent, w]
  calc
    _ = (G.induce {v : V | v ≠ z}).connectedComponentMk x :=
      ConnectedComponent.sound hreach
    _ = C := C.out_eq

noncomputable def neighborEquivPuncturedComponents {G : SimpleGraph V} {z : V}
    (htree : G.IsTree) :
    G.neighborSet z ≃ (G.induce {x | x ≠ z}).ConnectedComponent :=
  Equiv.ofBijective (puncturedNeighborComponent G z)
    ⟨puncturedNeighborComponent_injective htree.isAcyclic,
      puncturedNeighborComponent_surjective htree.connected⟩

noncomputable def puncturedComponentNeighbor {G : SimpleGraph V} {z : V}
    (htree : G.IsTree)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) : G.neighborSet z :=
  (neighborEquivPuncturedComponents htree).symm C

noncomputable def puncturedComponentRoot {G : SimpleGraph V} {z : V}
    (htree : G.IsTree)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) : C := by
  let w := puncturedComponentNeighbor htree C
  have hw : G.Adj z w.1 := w.2
  refine ⟨⟨w.1, hw.ne'⟩, ?_⟩
  change (G.induce {x | x ≠ z}).connectedComponentMk
    ⟨w.1, hw.ne'⟩ = C
  have h := (neighborEquivPuncturedComponents htree).apply_symm_apply C
  exact h

/--
@isnad1 id=eq.3h3v.s8.09221cb17baf from=translated src=- shape=e58d7dbd vocab=53e83121
-/
theorem card_puncturedComponents_eq_three
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected)
    {z : V} (hz : G.degree z = 3) :
    Fintype.card (G.induce {x | x ≠ z}).ConnectedComponent = 3 := by
  classical
  have htree : G.IsTree := ⟨hconn, hpos.isAcyclic⟩
  rw [← Fintype.card_congr (neighborEquivPuncturedComponents htree)]
  simp only [SimpleGraph.card_neighborSet_eq_degree, hz]

structure OrientedPuncturedArm (G : SimpleGraph V) (z : V) (htree : G.IsTree) where
  component : (G.induce {x | x ≠ z}).ConnectedComponent
  length : ℕ
  coord : pathGraph length ≃g component.toSimpleGraph
  zero : Fin length
  zero_val : zero.1 = 0
  coord_zero : coord zero = puncturedComponentRoot htree component

namespace OrientedPuncturedArm

variable {G : SimpleGraph V} {z : V} {htree : G.IsTree}

/--
@isnad1 id=lt.1h4v.s4.9063cd77ad9b from=translated src=- shape=9c59a2b5 vocab=e2267565
-/
theorem length_pos (A : OrientedPuncturedArm G z htree) : 0 < A.length :=
  by
    have h := A.zero.isLt
    rw [A.zero_val] at h
    exact h

def vertex (A : OrientedPuncturedArm G z htree) (i : Fin A.length) : V :=
  (A.coord i).1.1

/--
@isnad1 id=injectiv.1h4v.s5.b19a12b094b6 from=translated src=- shape=6ce0524e vocab=4486e6da
-/
theorem vertex_injective (A : OrientedPuncturedArm G z htree) :
    Function.Injective A.vertex := by
  intro i j hij
  apply A.coord.injective
  apply Subtype.ext
  apply Subtype.ext
  exact hij

/--
@isnad1 id=ne.1h5v.s5.3dbb49f038eb from=translated src=- shape=e5d11335 vocab=e82ddf58
-/
theorem vertex_ne_center (A : OrientedPuncturedArm G z htree) (i) :
    A.vertex i ≠ z :=
  (A.coord i).1.2

/--
@isnad1 id=adj.2h6v.s6.61e148307222 from=translated src=- shape=e48df383 vocab=f7527d44
-/
theorem adj_vertex_of_path_adj (A : OrientedPuncturedArm G z htree)
    {i j} (hij : (pathGraph A.length).Adj i j) :
    G.Adj (A.vertex i) (A.vertex j) := by
  exact A.coord.map_rel_iff.mpr hij

/--
@isnad1 id=adj.2h5v.s5.a8daa9043e6f from=translated src=- shape=88ea8bcf vocab=91b2c793
-/
theorem adj_center_vertex_of_val_eq_zero
    (A : OrientedPuncturedArm G z htree) (i) (hi : i.1 = 0) :
    G.Adj z (A.vertex i) := by
  have hiz : i = A.zero := Fin.ext (hi.trans A.zero_val.symm)
  subst i
  rw [vertex, A.coord_zero]
  exact (puncturedComponentNeighbor htree A.component).2

/--
@isnad1 id=ne.2h7v.s6.8682afbbda76 from=translated src=- shape=1c8a1841 vocab=a11160a3
-/
theorem vertex_ne_of_component_ne
    (A B : OrientedPuncturedArm G z htree)
    (hAB : A.component ≠ B.component) (i j) :
    A.vertex i ≠ B.vertex j := by
  intro hij
  apply hAB
  apply ConnectedComponent.eq_of_common_vertex (v := (A.coord i).1)
  · exact (A.coord i).2
  · have hv : (A.coord i).1 = (B.coord j).1 := Subtype.ext hij
    exact hv ▸ (B.coord j).2

def prefixEmbedding (A : OrientedPuncturedArm G z htree) {m : ℕ}
    (hm : m ≤ A.length) : Fin m ↪ V :=
  ⟨fun i ↦ A.vertex (Fin.castLE hm i), fun _ _ h ↦
    (Fin.castLEEmb hm).injective (A.vertex_injective h)⟩

/--
@isnad1 id=ne.2h6v.s5.4846050ea050 from=translated src=- shape=278d5f83 vocab=52caed73
-/
theorem prefixEmbedding_ne_center (A : OrientedPuncturedArm G z htree)
    {m : ℕ} (hm : m ≤ A.length) (i) : A.prefixEmbedding hm i ≠ z :=
  A.vertex_ne_center _

/--
@isnad1 id=ne.4h9v.s7.5e911cfccda3 from=translated src=- shape=895e7772 vocab=ba08b515
-/
theorem prefixEmbedding_ne_of_component_ne
    (A B : OrientedPuncturedArm G z htree)
    (hAB : A.component ≠ B.component)
    {m n : ℕ} (hm : m ≤ A.length) (hn : n ≤ B.length) (i j) :
    A.prefixEmbedding hm i ≠ B.prefixEmbedding hn j :=
  A.vertex_ne_of_component_ne B hAB _ _

/--
@isnad1 id=adj.3h7v.s6.11160fbc9d4d from=translated src=- shape=a1800197 vocab=a11fa6a7
-/
theorem adj_prefixEmbedding_of_path_adj
    (A : OrientedPuncturedArm G z htree) {m : ℕ}
    (hm : m ≤ A.length) {i j : Fin m} (hij : (pathGraph m).Adj i j) :
    G.Adj (A.prefixEmbedding hm i) (A.prefixEmbedding hm j) := by
  apply A.adj_vertex_of_path_adj
  rw [SimpleGraph.pathGraph_adj] at hij ⊢
  exact hij

/--
@isnad1 id=adj.3h6v.s6.5bd6553aa68b from=translated src=- shape=2b84974d vocab=47ad3d1a
-/
theorem adj_center_prefixEmbedding_of_val_eq_zero
    (A : OrientedPuncturedArm G z htree) {m : ℕ}
    (hm : m ≤ A.length) (i : Fin m) (hi : i.1 = 0) :
    G.Adj z (A.prefixEmbedding hm i) :=
  A.adj_center_vertex_of_val_eq_zero _ hi

end OrientedPuncturedArm

end Lattice
end SRG266
