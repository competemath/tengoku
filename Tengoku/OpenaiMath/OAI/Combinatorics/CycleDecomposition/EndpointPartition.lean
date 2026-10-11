import Tengoku.OpenaiMath.OAI.Combinatorics.CycleDecomposition.PathDeletion

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G := by
  classical
  obtain ⟨k,P,hd,hc,hk⟩ := Lovasz.path_cycle_partition G
  refine ⟨k,fun i => (P i).walk.edgeSet,?_,hd,hc,?_⟩
  · intro i
    rcases (P i).simple with hp | ⟨h,hcy⟩
    · exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
    · exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,hcy,by simp⟩
  · exact hk.trans (Finset.card_le_univ _)

theorem lovasz_theorem : MissingLovaszTheorem :=
  fun _ G => lovasz_path_cycle_partition G

end
end ErdosGallai

end
end
end

end OAI
