import Tengoku.Erdos64.Erdos64.Basic
import Tengoku.Erdos64.Erdos64.LeafBlocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/- A path in the complement of `C` connecting two ambient vertices. -/
def ExternalReachable
    {V : Type u} (G : SimpleGraph V) {s : V} (C : G.Walk s s)
    (x y : V) : Prop :=
  ∃ p : G.Walk x y, ∀ v, v ∈ p.support → v ∉ C.support

/- The ambient carrier of the complement component containing `x`. -/
def externalComponent
    {V : Type u} (G : SimpleGraph V) {s : V} (C : G.Walk s s)
    (x : V) (hx : x ∉ C.support) : Set V :=
  {y | y ∉ C.support ∧ ExternalReachable G C x y}

theorem ExternalReachable.refl
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x : V} (hx : x ∉ C.support) : ExternalReachable G C x x := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simpa using hx

theorem ExternalReachable.symm
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x y : V} (hxy : ExternalReachable G C x y) :
    ExternalReachable G C y x := by
  rcases hxy with ⟨p, hp⟩
  refine ⟨p.reverse, ?_⟩
  intro v hv
  apply hp v
  simpa [SimpleGraph.Walk.support_reverse] using hv

theorem ExternalReachable.trans
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x y z : V} (hxy : ExternalReachable G C x y)
    (hyz : ExternalReachable G C y z) :
    ExternalReachable G C x z := by
  rcases hxy with ⟨p, hp⟩
  rcases hyz with ⟨q, hq⟩
  refine ⟨p.append q, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hp v hv
  · exact hq v (List.mem_of_mem_tail hv)

theorem mem_externalComponent_self
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x : V} (hx : x ∉ C.support) :
    x ∈ externalComponent G C x hx := by
  exact ⟨hx, ExternalReachable.refl hx⟩

theorem externalComponent_adj_closure
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x u v : V} (hx : x ∉ C.support)
    (hu : u ∈ externalComponent G C x hx) (huv : G.Adj u v) :
    v ∈ C.support ∨ v ∈ externalComponent G C x hx := by
  rcases hu with ⟨huC, ⟨p, hp⟩⟩
  by_cases hvC : v ∈ C.support
  · exact Or.inl hvC
  · right
    refine ⟨hvC, ?_⟩
    refine ⟨p.append (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil), ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hp z hz
    · have hzv : z = v := by simpa using hz
      simpa [hzv] using hvC

theorem exists_adj_mem_of_mem_of_not_mem
    {V : Type u} {G : SimpleGraph V} {S : Set V}
    (hG : G.Connected) {x y : V} (hx : x ∈ S) (hy : y ∉ S) :
    ∃ u v, u ∈ S ∧ v ∉ S ∧ G.Adj u v := by
  by_contra hno
  have hnocross : ∀ {u v : V}, u ∈ S → v ∉ S → ¬G.Adj u v := by
    intro u v hu hv huv
    exact hno ⟨u, v, hu, hv, huv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath x y
  have hstay : ∀ {u v : V} (p : G.Walk u v), u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        exact hu
    | @cons u v w huv q ih =>
        intro hu
        have hv : v ∈ S := by
          by_contra hv
          exact hnocross hu hv huv
        exact ih hv
  exact hy (hstay p hx)

theorem externalComponent_exists_boundary
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    (_hC : C.IsCycle) (hG : G.Connected) {x : V} (hx : x ∉ C.support) :
    ∃ u, u ∈ externalComponent G C x hx ∧
      ∃ v, v ∈ C.support ∧ G.Adj u v := by
  have hxK : x ∈ externalComponent G C x hx :=
    mem_externalComponent_self hx
  have hsnotK : s ∉ externalComponent G C x hx := by
    intro hsK
    exact hsK.1 C.start_mem_support
  obtain ⟨u, v, hu, hv, huv⟩ :=
    exists_adj_mem_of_mem_of_not_mem hG hxK hsnotK
  rcases externalComponent_adj_closure hx hu huv with hvc | hvK
  · exact ⟨u, hu, v, hvc, huv⟩
  · exact (hv hvK).elim

theorem externalComponent_mem_of_mem_support
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
        have hz' : z = _ := List.mem_singleton.mp hz
        cases hz'
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
          · intro v hv
            exact hp v (List.mem_cons_of_mem _ hv)
          · exact hzq
  exact aux p ha hp hz

theorem externalComponent_induced_connected
    {V : Type u} {G : SimpleGraph V} {s : V} {C : G.Walk s s}
    {x : V} (hx : x ∉ C.support) :
    (G.induce (externalComponent G C x hx)).Connected := by
  letI : Nonempty (externalComponent G C x hx) :=
    ⟨⟨x, mem_externalComponent_self hx⟩⟩
  refine { preconnected := ?_ }
  intro u v
  rcases (ExternalReachable.symm u.property.2).trans v.property.2 with ⟨p, hp⟩
  have hpK : ∀ z, z ∈ p.support → z ∈ externalComponent G C x hx := by
    intro z hz
    exact externalComponent_mem_of_mem_support hx u.property p hp hz
  exact ⟨p.induce (externalComponent G C x hx) hpK⟩

theorem externalComponent_two_attachments_or_unique_root
    {V : Type u} {G : SimpleGraph V} {s : V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {C : G.Walk s s} (hC : C.IsCycle) (hG : G.Connected)
    {x : V} (hx : x ∉ C.support) :
    (∃ a b u v, a ∈ C.support ∧ b ∈ C.support ∧ a ≠ b ∧
      u ∈ externalComponent G C x hx ∧
      v ∈ externalComponent G C x hx ∧ G.Adj a u ∧ G.Adj b v) ∨
      ∃ r, r ∈ C.support ∧
        ∀ b, b ∈ C.support →
          ((∃ v, v ∈ externalComponent G C x hx ∧ G.Adj b v) ↔ b = r) := by
  let K : Set V := externalComponent G C x hx
  have hKconn : (G.induce K).Connected := by
    simpa [K] using externalComponent_induced_connected hx
  have hK_external : ∀ v, v ∈ K → v ∉ C.support := by
    intro v hv
    exact hv.1
  have hattach : ∃ a, a ∈ C.support ∧ ∃ u, u ∈ K ∧ G.Adj a u := by
    rcases externalComponent_exists_boundary hC hG hx with
      ⟨u, hu, v, hv, huv⟩
    exact ⟨v, hv, u, by simpa [K] using hu, huv.symm⟩
  simpa [K] using
    (external_carrier_two_attachments_or_unique_root hC K hKconn
      hK_external hattach)

end Erdos64
