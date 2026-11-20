/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.ClosedStarGluing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace SRG266.QuasiSymmetric.ConcreteQSD56

variable (Q : ConcreteQSD56)

set_option maxRecDepth 2048

noncomputable def canonicalBiplaneBlocks : Finset (Finset (Fin 56)) :=
  Finset.univ.image fun t : Fin 56 × Fin 11 => Q.toCoherentK11System.closedStar t.1 t.2

theorem mem_canonicalBiplaneBlocks {S : Finset (Fin 56)} :
    S ∈ Q.canonicalBiplaneBlocks ↔ ∃ p a, Q.toCoherentK11System.closedStar p a = S := by
  simp only [canonicalBiplaneBlocks, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists]

theorem canonicalBiplane_block_card {S : Finset (Fin 56)}
    (hS : S ∈ Q.canonicalBiplaneBlocks) : S.card = 11 := by
  obtain ⟨p,a,rfl⟩ := Q.mem_canonicalBiplaneBlocks.mp hS
  exact Q.toCoherentK11System.card_closedStar p a

theorem mem_canonicalBiplaneBlocks_iff_triple_clique {S : Finset (Fin 56)} :
    S ∈ Q.canonicalBiplaneBlocks ↔ S.card = 11 ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
        x ≠ y → x ≠ z → y ≠ z → Q.sparseTriple x y z := by
  constructor
  · intro hS
    refine ⟨Q.canonicalBiplane_block_card hS, ?_⟩
    obtain ⟨p,a,rfl⟩ := Q.mem_canonicalBiplaneBlocks.mp hS
    exact fun _ hx _ hy _ hz => Q.closedStar_triple_sparse hx hy hz
  · rintro ⟨hcard,hclique⟩
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    obtain ⟨a,ha⟩ := Q.eq_closedStar_of_triple_clique hcard hclique hp
    exact Q.mem_canonicalBiplaneBlocks.mpr ⟨p,a,ha.symm⟩

theorem card_filter_canonicalBiplane_at (p : Fin 56) (R : Finset (Fin 56) → Prop)
    [DecidablePred R] :
    (Q.canonicalBiplaneBlocks.filter fun S => p ∈ S ∧ R S).card =
      (Finset.univ.filter fun a : Fin 11 => R (Q.toCoherentK11System.closedStar p a)).card := by
  classical
  symm
  refine Finset.card_bij (fun a _ => Q.toCoherentK11System.closedStar p a) ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Q.mem_canonicalBiplaneBlocks.mpr ⟨p,a,rfl⟩,
      Q.toCoherentK11System.root_mem_closedStar p a, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb h
    exact Q.toCoherentK11System.closedStar_injective p h
  · intro S hS
    obtain ⟨hS,hp,hR⟩ := Finset.mem_filter.mp hS
    obtain ⟨q,b,rfl⟩ := Q.mem_canonicalBiplaneBlocks.mp hS
    obtain ⟨a,ha⟩ := Q.closedStar_reroot hp
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha ▸ hR⟩, ha.symm⟩

theorem canonicalBiplane_replication (p : Fin 56) :
    (Q.canonicalBiplaneBlocks.filter fun S => p ∈ S).card = 11 := by
  have h := Q.card_filter_canonicalBiplane_at p (fun _ => True)
  simpa using h

theorem canonicalBiplane_point_pair {p q : Fin 56} (hpq : p ≠ q) :
    (Q.canonicalBiplaneBlocks.filter fun S => p ∈ S ∧ q ∈ S).card = 2 := by
  rw [Q.card_filter_canonicalBiplane_at]
  have heq : (Finset.univ.filter fun a => q ∈ Q.toCoherentK11System.closedStar p a) =
      (Q.toCoherentK11System.coordinate p ⟨q,hpq.symm⟩).vertices := by
    ext a
    simp [Q.toCoherentK11System.coordinate_mem_closedStar p ⟨q,hpq.symm⟩ a]
  rw [heq, Edge11.card_vertices]

theorem canonicalBiplane_card : Q.canonicalBiplaneBlocks.card = 56 := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset (Fin 56))) (t := Q.canonicalBiplaneBlocks)
    (fun p S => p ∈ S)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at h
  rw [Finset.sum_congr rfl (fun p _ => Q.canonicalBiplane_replication p)] at h
  have hright : ∀ S ∈ Q.canonicalBiplaneBlocks,
      (Finset.univ.filter fun p => p ∈ S).card = 11 := by
    intro S hS
    simpa using Q.canonicalBiplane_block_card hS
  rw [Finset.sum_congr rfl hright] at h
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at h
  omega

theorem canonicalBiplane_block_pair {S T : Finset (Fin 56)}
    (hS : S ∈ Q.canonicalBiplaneBlocks) (hT : T ∈ Q.canonicalBiplaneBlocks)
    (hST : S ≠ T) : (S ∩ T).card = 2 := by
  obtain ⟨p,a,rfl⟩ := Q.mem_canonicalBiplaneBlocks.mp hS
  obtain ⟨q,b,rfl⟩ := Q.mem_canonicalBiplaneBlocks.mp hT
  have hmod := Q.closedStar_overlap_mod_three p q a b
  have hpos : 0 < (Q.toCoherentK11System.closedStar p a ∩
      Q.toCoherentK11System.closedStar q b).card := by
    by_contra hz
    have hz' : (Q.toCoherentK11System.closedStar p a ∩
        Q.toCoherentK11System.closedStar q b).card = 0 := by omega
    rw [hz'] at hmod
    exact (by decide : (0 : ZMod 3) ≠ 2) hmod
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
  obtain ⟨c,hc⟩ := Q.closedStar_reroot hxS
  obtain ⟨d,hd⟩ := Q.closedStar_reroot hxT
  have hcd : c ≠ d := fun h => hST (hc.trans ((congrArg _ h).trans hd.symm))
  rw [hc, hd, Q.toCoherentK11System.closedStar_inter_card x hcd]

theorem canonicalBiplane_triple_card (p : Fin 56)
    (q r : {x : Fin 56 // x ≠ p}) :
    (Q.canonicalBiplaneBlocks.filter fun S => p ∈ S ∧ q.val ∈ S ∧ r.val ∈ S).card =
      Edge11.vmeet (Q.toCoherentK11System.coordinate p q)
        (Q.toCoherentK11System.coordinate p r) := by
  rw [Q.card_filter_canonicalBiplane_at]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    Q.toCoherentK11System.coordinate_mem_closedStar p q a,
    Q.toCoherentK11System.coordinate_mem_closedStar p r a]

theorem canonicalBiplane_triple_complement {p q r : Fin 56}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Q.tripleMultiplicity p q r +
      (Q.canonicalBiplaneBlocks.filter fun S => p ∈ S ∧ q ∈ S ∧ r ∈ S).card = 2 := by
  rw [Q.canonicalBiplane_triple_card p ⟨q,hpq.symm⟩ ⟨r,hpr.symm⟩]
  let q' := neEquivPunctured p ⟨q,hpq.symm⟩
  let r' := neEquivPunctured p ⟨r,hpr.symm⟩
  have h := (Q.derived45 p).pairMult_add_vmeet_edgeEquiv q' r'
  have hne : q' ≠ r' := fun h => hqr (congrArg Subtype.val h)
  rw [Q.derived_pairMult_eq_tripleMultiplicity, ite_eq_right hne, add_zero] at h
  exact h

theorem localEdges_pointsOn_derived (p : Fin 56) (i : Fin 45) :
    Q.toCoherentK11System.localEdges (Q.pointsOn (Q.derivedEnum p i)) p =
      (Q.derived45 p).coverMember i := by
  classical
  ext e
  simp only [CoherentK11System.localEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_pointsOn, Derived45.mem_coverMember]
  change _ ↔ (Q.derived45 p).edgeEquiv.symm e ∈ Q.restrictedBlock p (Q.derivedEnum p i)
  rw [mem_restrictedBlock]
  rfl

theorem canonicalBiplane_old_block_intersections {S : Finset (Fin 56)}
    (hS : S ∈ Q.canonicalBiplaneBlocks) (B : Fin 210) :
    (Q.pointsOn B ∩ S).card = 0 ∨ (Q.pointsOn B ∩ S).card = 3 := by
  by_cases hz : (Q.pointsOn B ∩ S).card = 0
  · exact Or.inl hz
  right
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  obtain ⟨hpB,hpS⟩ := Finset.mem_inter.mp hp
  obtain ⟨q,a,rfl⟩ := Q.mem_canonicalBiplaneBlocks.mp hS
  obtain ⟨b,hb⟩ := Q.closedStar_reroot hpS
  rw [hb, Q.toCoherentK11System.card_inter_closedStar hpB]
  obtain ⟨i,hi⟩ := (derivedEnum_range (Q := Q) (z := p) B).mp
    (Q.mem_derivedIndex.mpr (Q.mem_pointsOn.mp hpB))
  rw [← hi, Q.localEdges_pointsOn_derived]
  change ((Q.derived45 p).coverMember i |>.filter fun e => b ∈ e.vertices).card + 1 = 3
  rw [(Q.derived45 p).two_regular_coverMember]

end SRG266.QuasiSymmetric.ConcreteQSD56
