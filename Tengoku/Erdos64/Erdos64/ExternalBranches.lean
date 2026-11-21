import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/- A connected external induced set joined to two distinct cycle vertices
   supplies an external bridge path. All separation and attachment data are
   explicit; no minimum-degree or global-connectivity premise is used. -/
noncomputable def CycleBridgePath.of_connected_external_set
    {V : Type u} {G : SimpleGraph V} {s : V}
    {C : G.Walk s s} (hC : C.IsCycle) (K : Set V)
    (hKconn : (G.induce K).Connected)
    {a b x y : V}
    (haC : a ∈ C.support) (hbC : b ∈ C.support) (hab : a ≠ b)
    (hxK : x ∈ K) (hyK : y ∈ K)
    (hax : G.Adj a x) (hby : G.Adj b y)
    (hK_external : ∀ v, v ∈ K → v ∉ C.support) :
    CycleBridgePath G C := by
  let hpath := hKconn.exists_isPath
    (⟨x, hxK⟩ : K) (⟨y, hyK⟩ : K)
  let r := Classical.choose hpath
  have hr : r.IsPath := Classical.choose_spec hpath
  let e : G.induce K →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  let r' : G.Walk x y := r.map e
  have hr' : r'.IsPath :=
    (SimpleGraph.Walk.isPath_map_iff_of_injective
      (f := e) Subtype.val_injective).mpr hr
  have hr'_external : ∀ v, v ∈ r'.support → v ∈ K := by
    intro v hv
    change v ∈ (r.map e).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    change (u : V) ∈ K
    exact u.property
  have hb_not_mem : b ∉ r'.support := by
    intro hb
    exact hK_external b (hr'_external b hb) hbC
  let p : G.Walk x b := r'.concat hby.symm
  have hp : p.IsPath := hr'.concat hb_not_mem hby.symm
  have ha_not_mem : a ∉ p.support := by
    intro ha
    have ha' : a ∈ r'.support ∨ a = b := by
      simpa [p] using ha
    rcases ha' with ha' | rfl
    · exact hK_external a (hr'_external a ha') haC
    · exact hab rfl
  let ear : G.Walk a b := SimpleGraph.Walk.cons hax p
  have hear : ear.IsPath := by
    exact (SimpleGraph.Walk.cons_isPath_iff hax p).2 ⟨hp, ha_not_mem⟩
  have hear_external : ear.support.tail.dropLast.Disjoint C.support := by
    apply List.disjoint_left.2
    intro v hv_ear hvC
    have hv_r : v ∈ r'.support := by
      simpa [ear, p, SimpleGraph.Walk.dropLast_support_concat] using hv_ear
    exact (hK_external v (hr'_external v hv_r)) hvC
  refine
    { left := a
      right := b
      left_mem_cycle := haC
      right_mem_cycle := hbC
      distinct_attachments := hab
      path := ear
      isPath := hear
      interior_disjoint_cycle := hear_external }

end Erdos64
