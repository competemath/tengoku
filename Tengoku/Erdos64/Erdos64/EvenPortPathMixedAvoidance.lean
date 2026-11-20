import Tengoku.Erdos64.Erdos64.OddOffPathComponent
import Tengoku.Erdos64.Erdos64.OddCarrierBoundaryAvoidance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In an all-odd-degree cut side, an even simple port path whose vertices
are cubic has a fresh dyadic or dyadic-successor ear avoiding any specified
path vertex. An odd-order off-path component is produced, so no component
witness or boundary-cardinality hypothesis is required.-/
theorem MinimalCounterexample.rootDeleted_even_port_path_mixed_ear_avoiding_vertex
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    (hodd : ∀ v, v ∈ rootDeletedComponentCarrier G r C → Odd (G.degree v))
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath) (heven : Even p.length)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (hcubic : ∀ v, v ∈ p.support → G.degree v = 3)
    (s : V) (hs : s ∈ p.support) :
    ∃ E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent,
      Odd (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E).card ∧
      ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
        1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
        ear.IsPath ∧ (ear.length = 2 ^ k ∨ ear.length = 2 ^ k + 1) ∧
        (∀ v, v ∈ ear.support → v = a ∨ v = b ∨
          v ∈ offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E) ∧
        (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
        (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C) ∧
        s ∉ ear.support := by
  classical
  obtain ⟨E, hKodd⟩ := M.rootDeleted_even_path_odd_offPathComponent r C D hCD
    hodd p hp heven hinside
  let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
  obtain ⟨_, hKdata, hboundary, hsize⟩ :=
    cut_side_offPath_carrier_data M r C D hCD hxy hrx hry p hinside E
  have hattachments : ∀ w, w ∈ p.support → ∀ a, a ∈ K → ∀ b, b ∈ K →
      G.Adj a w → G.Adj b w → a = b := by
    intro w hw a ha b hb haw hbw
    exact cut_side_port_path_external_neighbors_eq r C hxy hrx hry p hp hinside
      K hKdata w hw (hcubic w hw) a ha b hb haw.symm hbw.symm
  obtain ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh, hav⟩ :=
    M.odd_carrier_mixed_ear_avoiding_attachment K {v | v ∈ p.support}
      (fun v hv => (hKdata v hv).2) hboundary hKodd
      (fun v hv => hodd v (hKdata v hv).1) hsize hattachments s hs
  refine ⟨E, hKodd, k, a, b, ear, hk, ha, hb, hab, hear, hlen,
    hsupport, hfresh, ?_, hav⟩
  intro v hv
  rcases hsupport v hv with h | h | h
  · subst v
    exact hinside a ha
  · subst v
    exact hinside b hb
  · exact (hKdata v h).1

end Erdos64
