import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A root-deleted component with exactly two attachments supplies distinct
    root-attached endpoints and an ambient simple path contained in its carrier.
    The path has positive length; adjacent ports may still give length one.-/
theorem rootDeletedComponent_twoPort_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hcard : (rootDeletedComponentAttachments G r C).card = 2) :
    ∃ a b : V, ∃ p : G.Walk a b,
      a ≠ b ∧
      a ∈ rootDeletedComponentCarrier G r C ∧
      b ∈ rootDeletedComponentCarrier G r C ∧
      G.Adj r a ∧ G.Adj r b ∧
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C) ∧
      r ∉ p.support ∧ 0 < p.length := by
  classical
  obtain ⟨a, b, hab, ha, hb, hra, hrb⟩ :=
    rootDeletedComponent_twoPort_extraction r C hcard
  obtain ⟨har, haC⟩ := (mem_rootDeletedComponentCarrier_iff G r C a).mp ha
  obtain ⟨hbr, hbC⟩ := (mem_rootDeletedComponentCarrier_iff G r C b).mp hb
  obtain ⟨q, hq⟩ := C.connected_toSimpleGraph.exists_isPath
    (⟨⟨a, har⟩, haC⟩ : C) (⟨⟨b, hbr⟩, hbC⟩ : C)
  let e : C.toSimpleGraph →g G :=
    { toFun := fun v => v.1.1
      map_rel' := fun h => h }
  have he : Function.Injective e := by
    intro x y hxy
    change x.1.1 = y.1.1 at hxy
    exact Subtype.ext (Subtype.ext hxy)
  let p : G.Walk a b := q.map e
  have hp : p.IsPath :=
    (SimpleGraph.Walk.isPath_map_iff_of_injective (f := e) he).mpr hq
  have hinside : ∀ v, v ∈ p.support →
      v ∈ rootDeletedComponentCarrier G r C := by
    intro v hv
    change v ∈ (q.map e).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨z, _hz, rfl⟩ := List.mem_map.mp hv
    change z.1.1 ∈ rootDeletedComponentCarrier G r C
    exact (mem_rootDeletedComponentCarrier_iff G r C z.1.1).mpr
      ⟨z.1.2, z.2⟩
  have hroot : r ∉ p.support := by
    intro hrp
    exact (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
      (hinside r hrp)
  have hpos : 0 < p.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hab (SimpleGraph.Walk.eq_of_length_eq_zero hzero)
  exact ⟨a, b, p, hab, ha, hb, hra, hrb, hp, hinside, hroot, hpos⟩

end Erdos64
