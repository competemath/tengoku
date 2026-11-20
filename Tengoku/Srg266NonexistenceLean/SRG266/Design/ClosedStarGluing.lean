/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.CanonicalBiplaneCode
import Tengoku.Srg266NonexistenceLean.SRG266.Design.ClosedStarLinkParity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.QuasiSymmetric

open scoped BigOperators

/--
@isnad1 id=iff.0h3v.s4.393e8cf938d1 from=translated src=- shape=a2569baf vocab=e3b0c442
-/
theorem three_iff_parity (A B C : Prop) :
    ((A ↔ B) ↔ ((A ↔ C) ↔ (B ↔ C))) := by tauto

namespace Edge11

/--
@isnad1 id=eq.1h2v.s5.4de9266f14c2 from=translated src=- shape=e7093c5b vocab=fe828aa6
-/
theorem arcDegree_star_ne {a b : Fin 11} (hab : a ≠ b) :
    arcDegree (star a) b = 1 := by
  rw [arcDegree, Finset.card_eq_one]
  refine ⟨mk' hab, ?_⟩
  ext e
  simp only [Finset.mem_filter, mem_star, Finset.mem_singleton]
  constructor
  · intro h
    exact eq_of_mem_mem hab h.1 h.2
  · rintro rfl
    simp [vertices_mk']

/--
@isnad1 id=le.2h3v.s6.4be94b2263cd from=translated src=- shape=0cb6f624 vocab=1ca4d2c6
-/
theorem degree_le_two_of_meets {T : Finset Edge11} {c : Edge11}
    (htouch : ∀ e ∈ T, e = c ∨ vmeet c e = 1)
    {w : Fin 11} (hw : w ∉ c.vertices) : arcDegree T w ≤ 2 := by
  obtain ⟨u, v, huv, hc⟩ := Finset.card_eq_two.mp (card_vertices c)
  have hwu : w ≠ u := by intro h; subst w; simp [hc] at hw
  have hwv : w ≠ v := by intro h; subst w; simp [hc] at hw
  have hsub : (T.filter fun e => w ∈ e.vertices) ⊆
      {mk' hwu, mk' hwv} := by
    intro e he
    obtain ⟨heT, hwe⟩ := Finset.mem_filter.mp he
    rcases htouch e heT with rfl | hmeet
    · exact False.elim (hw hwe)
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < vmeet c e by omega)
      have hxx := Finset.mem_inter.mp hx
      rw [hc] at hxx
      have hxuv : x = u ∨ x = v := by simpa using hxx.1
      rcases hxuv with rfl | rfl
      · simp [eq_of_mem_mem hwu hwe hxx.2]
      · simp [eq_of_mem_mem hwv hwe hxx.2]
  have hcard : ({mk' hwu, mk' hwv} : Finset Edge11).card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  exact (Finset.card_le_card hsub).trans hcard

/--
@isnad1 id=mem.7h5v.s8.c437459c8cc0 from=translated src=- shape=0bf76c99 vocab=2c5a8863
-/
theorem common_endpoint_mem_central {T : Finset Edge11} {c e f : Edge11}
    (htouch : ∀ e ∈ T, e = c ∨ vmeet c e = 1)
    (hdegree : ∀ w, (arcDegree T w : ZMod 3) = 1)
    (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f)
    {w : Fin 11} (hwe : w ∈ e.vertices) (hwf : w ∈ f.vertices) :
    w ∈ c.vertices := by
  by_contra hw
  have hle := degree_le_two_of_meets htouch hw
  have hge : 2 ≤ arcDegree T w := by
    apply Nat.succ_le_of_lt
    apply Finset.one_lt_card.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hwe⟩,
      f, Finset.mem_filter.mpr ⟨hf, hwf⟩, hef⟩
  have hn : arcDegree T w = 2 := by omega
  have h := hdegree w
  rw [hn] at h
  exact (by decide : (2 : ZMod 3) ≠ 1) h

/--
@isnad1 id=iff.9h6v.s8.7e28b8a0be36 from=translated src=- shape=2f70c81f vocab=cb82e7ab
-/
theorem vmeet_eq_one_iff_same_side {T : Finset Edge11} {c e f : Edge11}
    (htouch : ∀ e ∈ T, e = c ∨ vmeet c e = 1)
    (hdegree : ∀ w, (arcDegree T w : ZMod 3) = 1)
    (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f)
    (hec : e ≠ c) (hfc : f ≠ c)
    {u v : Fin 11} (huv : u ≠ v) (hc : c.vertices = {u,v}) :
    vmeet e f = 1 ↔ (u ∈ e.vertices ↔ u ∈ f.vertices) := by
  have hnotboth : ∀ g : Edge11, g ≠ c → u ∈ g.vertices → v ∉ g.vertices := by
    intro g hgc hgu hgv
    apply hgc
    exact (eq_of_mem_mem huv hgu hgv).trans
      (eq_of_mem_mem huv (by simp [hc]) (by simp [hc])).symm
  have hone : ∀ g ∈ T, g ≠ c → u ∈ g.vertices ∨ v ∈ g.vertices := by
    intro g hg hgc
    have hcg := (htouch g hg).resolve_left hgc
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < vmeet c g by omega)
    have hww := Finset.mem_inter.mp hw
    rw [hc] at hww
    have hwuv : w = u ∨ w = v := by simpa using hww.1
    rcases hwuv with rfl | rfl
    · exact Or.inl hww.2
    · exact Or.inr hww.2
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < vmeet e f by omega)
    obtain ⟨hwe, hwf⟩ := Finset.mem_inter.mp hw
    have hwc := common_endpoint_mem_central htouch hdegree he hf hef hwe hwf
    rw [hc] at hwc
    have hwuv : w = u ∨ w = v := by simpa using hwc
    rcases hwuv with rfl | rfl
    · exact iff_of_true hwe hwf
    · exact iff_of_false (fun h => hnotboth e hec h hwe)
        (fun h => hnotboth f hfc h hwf)
  · intro h
    by_cases hue : u ∈ e.vertices
    · exact vmeet_eq_one hef hue (h.mp hue)
    · have huf : u ∉ f.vertices := fun hf => hue (h.mpr hf)
      exact vmeet_eq_one hef ((hone e he hec).resolve_left hue)
        ((hone f hf hfc).resolve_left huf)

/--
@isnad1 id=ex.2h1v.s6.3ddd5f546e16 from=translated src=- shape=17372aa6 vocab=a7c631d2
-/
theorem exists_star_of_pairwise {T : Finset Edge11} (hcard : 3 < T.card)
    (hpair : ∀ e ∈ T, ∀ f ∈ T, e ≠ f → vmeet e f = 1) :
    ∃ w : Fin 11, T ⊆ star w := by
  obtain ⟨c, hcT⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  obtain ⟨u, v, huv, hc⟩ := Finset.card_eq_two.mp (card_vertices c)
  have hsum : arcDegree T u + arcDegree T v = T.card + 1 := by
    calc
      _ = ∑ f ∈ T, vmeet c f := by
        rw [sum_vmeet_left, hc, Finset.sum_pair huv]
      _ = ∑ f ∈ T, (1 + if f = c then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro f hf
        by_cases hfc : f = c
        · simp [hfc, vmeet_self]
        · simp [hfc, hpair c hcT f hf (Ne.symm hfc)]
      _ = T.card + 1 := by simp [Finset.sum_add_distrib, hcT]
  have hhigh : 3 ≤ arcDegree T u ∨ 3 ≤ arcDegree T v := by omega
  obtain ⟨w, hw⟩ : ∃ w, 3 ≤ arcDegree T w := by
    rcases hhigh with hu | hv
    · exact ⟨u, hu⟩
    · exact ⟨v, hv⟩
  refine ⟨w, ?_⟩
  intro e he
  apply mem_star.mpr
  by_contra hwe
  have htouch : ∀ f ∈ T, f = e ∨ vmeet e f = 1 := by
    intro f hf
    by_cases hfe : f = e
    · exact Or.inl hfe
    · exact Or.inr (hpair e he f hf (Ne.symm hfe))
  have hlow := degree_le_two_of_meets htouch hwe
  omega

end Edge11

namespace CoherentK11System

variable {P : Type*} [DecidableEq P] (K : CoherentK11System P)

/--
@isnad1 id=eq.0h4v.s5.2a7f17aff75e from=translated src=- shape=076263ac vocab=a7a9f7d0
-/
theorem localEdges_closedStar (p : P) (a : Fin 11) :
    K.localEdges (K.closedStar p a) p = Edge11.star a := by
  ext e
  have h := K.coordinate_mem_closedStar p ((K.coordinate p).symm e) a
  simpa [localEdges] using h

/--
@isnad1 id=injectiv.0h3v.s4.c4ca441eedb7 from=translated src=- shape=7ea29a5c vocab=80b7fef7
-/
theorem closedStar_injective (p : P) : Function.Injective (K.closedStar p) := by
  intro a b hab
  by_contra hne
  obtain ⟨c, hc⟩ : ∃ c : Fin 11, c ≠ a ∧ c ≠ b := by
    have hlt : ({a,b} : Finset (Fin 11)).card < (Finset.univ : Finset (Fin 11)).card := by
      have hle := Finset.card_le_two (a := a) (b := b)
      simpa using (show ({a,b} : Finset (Fin 11)).card < 11 by omega)
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨c, by simpa using hc⟩
  let q := (K.coordinate p).symm (Edge11.mk' hc.1.symm)
  have hqa : q.val ∈ K.closedStar p a := by
    apply (K.coordinate_mem_closedStar p q a).mpr
    simp [q, Edge11.vertices_mk']
  rw [hab] at hqa
  have hqb := (K.coordinate_mem_closedStar p q b).mp hqa
  simp [q, Edge11.vertices_mk', Ne.symm hne, Ne.symm hc.2] at hqb

/--
@isnad1 id=eq.1h5v.s6.0d7084fbe1a3 from=translated src=- shape=db136cce vocab=15eb646c
-/
theorem card_inter_closedStar {S : Finset P} {q : P} (hq : q ∈ S) (v : Fin 11) :
    (S ∩ K.closedStar q v).card = arcDegree (K.localEdges S q) v + 1 := by
  classical
  have hcard : arcDegree (K.localEdges S q) v =
      ((S ∩ K.closedStar q v).erase q).card := by
    refine Finset.card_bij
      (fun e _ => ((K.coordinate q).symm e).val) ?_ ?_ ?_
    · intro e he
      obtain ⟨heT, hve⟩ := Finset.mem_filter.mp he
      have heroot := ((K.coordinate q).symm e).property
      refine Finset.mem_erase.mpr ⟨heroot, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact (Finset.mem_filter.mp heT).2
      · apply (K.coordinate_mem_closedStar q ((K.coordinate q).symm e) v).mpr
        simpa using hve
    · intro e he f hf h
      exact (K.coordinate q).symm.injective (Subtype.ext h)
    · intro x hx
      obtain ⟨hxq, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxS, hxstar⟩ := Finset.mem_inter.mp hx
      let x' : {x : P // x ≠ q} := ⟨x, hxq⟩
      refine ⟨K.coordinate q x', Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (K.coordinate_mem_localEdges S q x').mpr hxS
      · exact (K.coordinate_mem_closedStar q x' v).mp hxstar
      · simp [x']
  rw [hcard, Finset.card_erase_of_mem
    (Finset.mem_inter.mpr ⟨hq, K.root_mem_closedStar q v⟩)]
  have hpos : 0 < (S ∩ K.closedStar q v).card :=
    Finset.card_pos.mpr ⟨q, Finset.mem_inter.mpr ⟨hq, K.root_mem_closedStar q v⟩⟩
  omega

/--
@isnad1 id=or.2h6v.s8.c6e2c0eb9b23 from=translated src=- shape=38210e10 vocab=671727eb
-/
theorem localEdges_closedStar_meets {p : P} {a : Fin 11}
    (q : {q : P // q ≠ p}) (hq : q.val ∈ K.closedStar p a) :
    ∀ e ∈ K.localEdges (K.closedStar p a) q.val,
      e = K.coordinate q.val ⟨p, q.property.symm⟩ ∨
      Edge11.vmeet (K.coordinate q.val ⟨p, q.property.symm⟩) e = 1 := by
  intro e he
  let r := (K.coordinate q.val).symm e
  have hre : K.coordinate q.val r = e := (K.coordinate q.val).apply_symm_apply e
  have hrS : r.val ∈ K.closedStar p a := (Finset.mem_filter.mp he).2
  by_cases hrp : r.val = p
  · left
    rw [← hre]
    exact congrArg (K.coordinate q.val) (Subtype.ext hrp)
  · right
    rw [← hre]
    apply (K.coherent q.property hrp r.property).mp
    apply Edge11.vmeet_eq_one
      (fun h => r.property (congrArg Subtype.val ((K.coordinate p).injective h)).symm)
      ((K.coordinate_mem_closedStar p q a).mp hq)
      ((K.coordinate_mem_closedStar p ⟨r.val, hrp⟩ a).mp hrS)

/--
@isnad1 id=eq.1h5v.s5.91da011753c0 from=translated src=- shape=949ff3d1 vocab=14718b9b
-/
theorem closedStar_inter_card (p : P) {a b : Fin 11} (hab : a ≠ b) :
    (K.closedStar p a ∩ K.closedStar p b).card = 2 := by
  rw [K.card_inter_closedStar (K.root_mem_closedStar p a),
    K.localEdges_closedStar, Edge11.arcDegree_star_ne hab]

end CoherentK11System

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

/--
@isnad1 id=eq.1h5v.s7.a0848909c5c1 from=translated src=- shape=f323a115 vocab=1973ad9d
-/
theorem closedStar_degree_mod_three {p q : Fin 56} {a : Fin 11}
    (hq : q ∈ Q.toCoherentK11System.closedStar p a) (w : Fin 11) :
    (arcDegree (Q.toCoherentK11System.localEdges
      (Q.toCoherentK11System.closedStar p a) q) w : ZMod 3) = 1 := by
  have h := Q.closedStar_overlap_mod_three p q a w
  rw [Q.toCoherentK11System.card_inter_closedStar hq, Nat.cast_add, Nat.cast_one] at h
  linear_combination h

/--
@isnad1 id=ex.2h4v.s9.34c266a0220a from=translated src=- shape=29038ef2 vocab=70c8bb27
-/
theorem closedStar_link_has_two_sides {p q : Fin 56} {a : Fin 11}
    (hqp : q ≠ p) (hq : q ∈ Q.toCoherentK11System.closedStar p a) :
    ∃ u : Fin 11, ∀ r s : {x : Fin 56 // x ≠ q},
      r.val ∈ Q.toCoherentK11System.closedStar p a →
      s.val ∈ Q.toCoherentK11System.closedStar p a →
      r.val ≠ p → s.val ≠ p → r ≠ s →
      (Q.sparseTriple q r s ↔
        (u ∈ (Q.toCoherentK11System.coordinate q r).vertices ↔
          u ∈ (Q.toCoherentK11System.coordinate q s).vertices)) := by
  let K := Q.toCoherentK11System
  let c := K.coordinate q ⟨p, hqp.symm⟩
  obtain ⟨u, v, huv, hc⟩ := Finset.card_eq_two.mp (Edge11.card_vertices c)
  refine ⟨u, ?_⟩
  intro r s hr hs hrp hsp hrs
  rw [← Q.coordinate_vmeet_iff_sparse q r s]
  apply Edge11.vmeet_eq_one_iff_same_side
    (K.localEdges_closedStar_meets ⟨q, hqp⟩ hq)
    (Q.closedStar_degree_mod_three hq)
    ((K.coordinate_mem_localEdges _ q r).mpr hr)
    ((K.coordinate_mem_localEdges _ q s).mpr hs)
    (fun h => hrs ((K.coordinate q).injective h))
    (fun h => hrp (congrArg Subtype.val ((K.coordinate q).injective h)))
    (fun h => hsp (congrArg Subtype.val ((K.coordinate q).injective h))) huv hc

/--
@isnad1 id=sparsetr.5h5v.s7.04329538d351 from=translated src=- shape=fd5bcfc7 vocab=53338295
-/
theorem closedStar_root_sparse {p q r : Fin 56} {a : Fin 11}
    (hq : q ∈ Q.toCoherentK11System.closedStar p a)
    (hr : r ∈ Q.toCoherentK11System.closedStar p a)
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r) : Q.sparseTriple p q r := by
  apply (Q.coordinate_vmeet_iff_sparse p ⟨q, hqp⟩ ⟨r, hrp⟩).mp
  exact Edge11.vmeet_eq_one
    (fun h => hqr (congrArg Subtype.val ((Q.toCoherentK11System.coordinate p).injective h)))
    ((Q.toCoherentK11System.coordinate_mem_closedStar p ⟨q,hqp⟩ a).mp hq)
    ((Q.toCoherentK11System.coordinate_mem_closedStar p ⟨r,hrp⟩ a).mp hr)

/--
@isnad1 id=iff.10h7v.s8.c0e292166722 from=translated src=- shape=b9b32e6e vocab=5e782516
-/
theorem closedStar_link_parity {p q x y z : Fin 56} {a : Fin 11}
    (hq : q ∈ (Q.toCoherentK11System.closedStar p a).erase p)
    (hx : x ∈ (Q.toCoherentK11System.closedStar p a).erase p)
    (hy : y ∈ (Q.toCoherentK11System.closedStar p a).erase p)
    (hz : z ∈ (Q.toCoherentK11System.closedStar p a).erase p)
    (hxq : x ≠ q) (hyq : y ≠ q) (hzq : z ≠ q)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (Q.sparseTriple q x y ↔ (Q.sparseTriple q x z ↔ Q.sparseTriple q y z)) := by
  obtain ⟨hqp, hq⟩ := Finset.mem_erase.mp hq
  obtain ⟨hxp, hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨hyp, hy⟩ := Finset.mem_erase.mp hy
  obtain ⟨hzp, hz⟩ := Finset.mem_erase.mp hz
  obtain ⟨u, hu⟩ := Q.closedStar_link_has_two_sides hqp hq
  have h₁ := hu ⟨x,hxq⟩ ⟨y,hyq⟩ hx hy hxp hyp
    (fun h => hxy (congrArg Subtype.val h))
  have h₂ := hu ⟨x,hxq⟩ ⟨z,hzq⟩ hx hz hxp hzp
    (fun h => hxz (congrArg Subtype.val h))
  have h₃ := hu ⟨y,hyq⟩ ⟨z,hzq⟩ hy hz hyp hzp
    (fun h => hyz (congrArg Subtype.val h))
  change (Q.sparseTriple q x y ↔ _) at h₁
  change (Q.sparseTriple q x z ↔ _) at h₂
  change (Q.sparseTriple q y z ↔ _) at h₃
  rw [h₁, h₂, h₃]
  exact three_iff_parity _ _ _

/--
@isnad1 id=sparsetr.6h6v.s7.9c122151a69d from=translated src=- shape=fedd41c9 vocab=53338295
-/
theorem closedStar_triple_sparse {p x y z : Fin 56} {a : Fin 11}
    (hx : x ∈ Q.toCoherentK11System.closedStar p a)
    (hy : y ∈ Q.toCoherentK11System.closedStar p a)
    (hz : z ∈ Q.toCoherentK11System.closedStar p a)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Q.sparseTriple x y z := by
  by_cases hxp : x = p
  · subst x
    exact Q.closedStar_root_sparse hy hz hxy.symm hxz.symm hyz
  by_cases hyp : y = p
  · subst y
    exact (Q.sparseTriple_swap p x z).mp
      (Q.closedStar_root_sparse hx hz hxp hyz.symm hxz)
  by_cases hzp : z = p
  · subst z
    exact (Q.sparseTriple_rotate p x y).mp
      (Q.closedStar_root_sparse hx hy hxp hyp hxy)
  let X := (Q.toCoherentK11System.closedStar p a).erase p
  have hX : X.card = 10 := by
    rw [Finset.card_erase_of_mem (Q.toCoherentK11System.root_mem_closedStar p a),
      Q.toCoherentK11System.card_closedStar]
  have hsmall : ({x,y,z} : Finset (Fin 56)).card < X.card := by
    have hle := Finset.card_le_three (a := x) (b := y) (c := z)
    omega
  obtain ⟨d, hd, hdnot⟩ := Finset.not_subset.mp
    (show ¬ X ⊆ {x,y,z} from fun h => Nat.not_le_of_gt hsmall (Finset.card_le_card h))
  have hdx : d ≠ x := by intro h; subst d; simp at hdnot
  have hdy : d ≠ y := by intro h; subst d; simp at hdnot
  have hdz : d ≠ z := by intro h; subst d; simp at hdnot
  have hxX : x ∈ X := Finset.mem_erase.mpr ⟨hxp,hx⟩
  have hyX : y ∈ X := Finset.mem_erase.mpr ⟨hyp,hy⟩
  have hzX : z ∈ X := Finset.mem_erase.mpr ⟨hzp,hz⟩
  exact triple_of_four_point_link_parity Q.sparseTriple Q.sparseTriple_swap
    Q.sparseTriple_rotate x y z d
    (Q.closedStar_link_parity hxX hyX hzX hd hxy.symm hxz.symm hdx hyz hdy.symm hdz.symm)
    (Q.closedStar_link_parity hyX hxX hzX hd hxy hyz.symm hdy hxz hdx.symm hdz.symm)
    (Q.closedStar_link_parity hzX hxX hyX hd hxz hyz hdz hxy hdx.symm hdy.symm)

theorem eq_closedStar_of_triple_clique {S : Finset (Fin 56)} {q : Fin 56}
    (hcard : S.card = 11)
    (hclique : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x ≠ y → x ≠ z → y ≠ z → Q.sparseTriple x y z)
    (hq : q ∈ S) : ∃ b : Fin 11, S = Q.toCoherentK11System.closedStar q b := by
  let K := Q.toCoherentK11System
  let T := K.localEdges S q
  have hT : T.card = 10 := by
    rw [K.card_localEdges, Finset.card_erase_of_mem hq, hcard]
  have hpair : ∀ e ∈ T, ∀ f ∈ T, e ≠ f → Edge11.vmeet e f = 1 := by
    intro e he f hf hef
    let r := (K.coordinate q).symm e
    let s := (K.coordinate q).symm f
    have hr : r.val ∈ S := (Finset.mem_filter.mp he).2
    have hs : s.val ∈ S := (Finset.mem_filter.mp hf).2
    have hrs : r.val ≠ s.val := fun h => hef
      ((K.coordinate q).symm.injective (Subtype.ext h))
    have h := hclique q hq r.val hr s.val hs r.property.symm s.property.symm hrs
    have hmeet := (Q.coordinate_vmeet_iff_sparse q r s).mpr h
    simpa [r, s, K] using hmeet
  obtain ⟨b, hb⟩ := Edge11.exists_star_of_pairwise (by omega : 3 < T.card) hpair
  have heq : T = Edge11.star b := Finset.eq_of_subset_of_card_le hb
    (by rw [Edge11.card_star, hT])
  refine ⟨b, ?_⟩
  ext x
  by_cases hxq : x = q
  · subst x
    exact iff_of_true hq (K.root_mem_closedStar q b)
  · have h₁ := K.coordinate_mem_localEdges S q ⟨x,hxq⟩
    have h₂ := K.coordinate_mem_closedStar q ⟨x,hxq⟩ b
    change K.coordinate q ⟨x,hxq⟩ ∈ T ↔ x ∈ S at h₁
    rw [heq, Edge11.mem_star] at h₁
    exact h₁.symm.trans h₂.symm

/--
@isnad1 id=ex.1h4v.s7.3aeb1cf46c7a from=translated src=- shape=47af8a7d vocab=588f57ad
-/
theorem closedStar_reroot {p q : Fin 56} {a : Fin 11}
    (hq : q ∈ Q.toCoherentK11System.closedStar p a) :
    ∃ b : Fin 11, Q.toCoherentK11System.closedStar p a =
      Q.toCoherentK11System.closedStar q b :=
  Q.eq_closedStar_of_triple_clique (Q.toCoherentK11System.card_closedStar p a)
    (fun _ hx _ hy _ hz => Q.closedStar_triple_sparse hx hy hz) hq

end ConcreteQSD56
end SRG266.QuasiSymmetric
