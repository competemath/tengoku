import Tengoku.Erdos64.Erdos64.ComponentAttachments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

theorem mem_externalComponent_of_mem_support
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x a b : V} (hx : x ∉ C.support)
    (ha : a ∈ externalComponent G C x hx)
    (p : G.Walk a b)
    (hp : ∀ v, v ∈ p.support → v ∉ C.support)
    {z : V} (hz : z ∈ p.support) :
    z ∈ externalComponent G C x hx := by
  have aux :
      ∀ {a b : V} (p : G.Walk a b),
        a ∈ externalComponent G C x hx →
        (∀ v, v ∈ p.support → v ∉ C.support) →
        ∀ {z}, z ∈ p.support → z ∈ externalComponent G C x hx := by
    intro a b p
    induction p with
    | nil =>
        intro ha hp z hz
        rw [SimpleGraph.Walk.support_nil] at hz
        have hzu : z = _ := List.mem_singleton.mp hz
        rw [hzu]
        exact ha
    | @cons a b c hab q ih =>
        intro ha hp z hz
        have hbmem : b ∈ (SimpleGraph.Walk.cons hab q).support := by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_of_mem_tail q.start_mem_support
        have hb : b ∈ externalComponent G C x hx := by
          rcases externalComponent_adj_closure hx ha hab with hbc | hbK
          · exact (hp b hbmem hbc).elim
          · exact hbK
        rw [SimpleGraph.Walk.support_cons] at hz
        rcases List.mem_cons.mp hz with hza | hzq
        · simpa [hza] using ha
        · apply ih hb
          intro v hv
          exact hp v (List.mem_cons_of_mem _ hv)
          exact hzq
  exact aux p ha hp hz

theorem externalComponent_exists_walk
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x a b : V} (hx : x ∉ C.support)
    (ha : a ∈ externalComponent G C x hx)
    (hb : b ∈ externalComponent G C x hx) :
    ∃ p : G.Walk a b, ∀ v, v ∈ p.support →
      v ∈ externalComponent G C x hx := by
  rcases (ExternalReachable.symm ha.2).trans hb.2 with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro v hv
  exact mem_externalComponent_of_mem_support hx ha p hp hv

theorem externalComponent_connected
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x : V} (hx : x ∉ C.support) :
    (G.induce (externalComponent G C x hx)).Connected := by
  letI : Nonempty (externalComponent G C x hx) :=
    ⟨⟨x, mem_externalComponent_self hx⟩⟩
  refine { preconnected := ?_ }
  intro u v
  obtain ⟨p, hp⟩ := externalComponent_exists_walk hx u.property v.property
  exact ⟨p.induce (externalComponent G C x hx) hp⟩

end Erdos64
