import Tengoku.Erdos64.Erdos64.ResidualPathSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- If a simple residual path contains the shared root internally, split it at
that unique root occurrence.  The two simple pieces have positive length,
concatenate back to the original path, and meet only at the root.-/
theorem residual_path_root_internal_split
    {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    {r u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hru : u ≠ r) (hrv : v ≠ r)
    (hrp : r ∈ p.support) :
    ∃ (a : G.Walk u r) (b : G.Walk r v),
      a.IsPath ∧ b.IsPath ∧
      a.append b = p ∧
      a.support ⊆ p.support ∧ b.support ⊆ p.support ∧
      a.length + b.length = p.length ∧
      0 < a.length ∧ 0 < b.length ∧
      r ∉ a.support.dropLast ∧ r ∉ b.support.tail := by
  let a : G.Walk u r := p.takeUntil r hrp
  let b : G.Walk r v := p.dropUntil r hrp
  have hab : a.append b = p := by
    dsimp [a, b]
    exact p.take_spec hrp
  have ha : a.IsPath := by
    dsimp [a]
    exact hp.takeUntil hrp
  have hb : b.IsPath := by
    dsimp [b]
    exact hp.dropUntil hrp
  have hnodup : (a.support.dropLast ++ b.support).Nodup := by
    rw [← SimpleGraph.Walk.support_append_eq_support_dropLast_append, hab]
    exact hp.support_nodup
  have hdisj₁ : a.support.dropLast.Disjoint b.support :=
    List.disjoint_of_nodup_append hnodup
  have hnodup' : (a.support ++ b.support.tail).Nodup := by
    rw [← SimpleGraph.Walk.support_append, hab]
    exact hp.support_nodup
  have hdisj₂ : a.support.Disjoint b.support.tail :=
    List.disjoint_of_nodup_append hnodup'
  have hra : r ∈ b.support := by simp [b]
  have hraa : r ∈ a.support := by simp [a]
  have hasub : a.support ⊆ p.support := by
    dsimp [a]
    exact p.support_takeUntil_subset_support hrp
  have hbsub : b.support ⊆ p.support := by
    dsimp [b]
    exact p.support_dropUntil_subset_support hrp
  have ha_nil : ¬ a.Nil := by
    rw [SimpleGraph.Walk.nil_takeUntil]
    exact hru
  have hb_nil : ¬ b.Nil := by
    intro hnil
    exact hrv ((SimpleGraph.Walk.Nil.eq hnil).symm)
  have ha_pos : 0 < a.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp ha_nil
  have hb_pos : 0 < b.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hb_nil
  refine ⟨a, b, ha, hb, hab, hasub, hbsub, ?_, ha_pos, hb_pos, ?_, ?_⟩
  · rw [← SimpleGraph.Walk.length_append, hab]
  · intro h
    exact (List.disjoint_left.mp hdisj₁ h hra).elim
  · intro h
    exact (List.disjoint_left.mp hdisj₂ hraa h).elim

/-- A root-avoiding simple path cannot leave a closed side: once its
start is in `D`, every support vertex remains in `D` because the only allowed
boundary exit is the distinguished root.-/
theorem SimpleGraph.Walk.IsPath.support_subset_of_boundary_avoiding_root
    {V : Type u} {G : SimpleGraph V}
    {D : Finset V} {r u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hstart : u ∈ D) (hroot : r ∉ p.support)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r) :
    ∀ z, z ∈ p.support → z ∈ D := by
  induction p with
  | nil =>
      intro z hz
      simp at hz
      subst z
      exact hstart
  | @cons a b d h q ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hstart
      · have hqpath : q.IsPath := hp.of_cons
        have hbD : b ∈ D := by
          by_contra hbD
          have hbr : b = r := hboundary a hstart b hbD h
          apply hroot
          have hbmem : b ∈ (SimpleGraph.Walk.cons h q).support := by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr q.start_mem_support
          simpa [hbr] using hbmem
        have hrootq : r ∉ q.support := by
          intro hrq
          apply hroot
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr hrq
        exact ih hqpath hbD hrootq z hz

/-- The interior of a positive path ending at the boundary root stays inside a
closed side when its start lies in that side.-/
theorem SimpleGraph.Walk.IsPath.dropLast_support_subset_of_boundary
    {V : Type u} {G : SimpleGraph V}
    {D : Finset V} {r u : V} {a : G.Walk u r}
    (ha : a.IsPath) (hpos : 0 < a.length) (hstart : u ∈ D)
    (hroot : r ∉ a.support.dropLast)
    (hboundary : ∀ x, x ∈ D → ∀ y, y ∉ D → G.Adj x y → y = r) :
    ∀ z, z ∈ a.support.dropLast → z ∈ D := by
  have hnil : ¬ a.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  have hdrop : r ∉ a.dropLast.support := by
    rw [SimpleGraph.Walk.support_dropLast hnil]
    exact hroot
  have hsubset := SimpleGraph.Walk.IsPath.support_subset_of_boundary_avoiding_root
    ha.dropLast hstart hdrop hboundary
  intro z hz
  apply hsubset z
  rw [SimpleGraph.Walk.support_dropLast hnil]
  exact hz

/-- The interior of a positive path starting at the boundary root stays inside
a closed side when its end lies in that side; reverse the path to apply the
preceding boundary argument.-/
theorem SimpleGraph.Walk.IsPath.tail_support_subset_of_boundary
    {V : Type u} {G : SimpleGraph V}
    {D : Finset V} {r v : V} {b : G.Walk r v}
    (hb : b.IsPath) (hpos : 0 < b.length) (hend : v ∈ D)
    (hroot : r ∉ b.support.tail)
    (hboundary : ∀ x, x ∈ D → ∀ y, y ∉ D → G.Adj x y → y = r) :
    ∀ z, z ∈ b.support.tail → z ∈ D := by
  have hnil : ¬ b.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  have hdrop : r ∉ b.reverse.dropLast.support := by
    rw [SimpleGraph.Walk.support_dropLast]
    · simp only [SimpleGraph.Walk.support_reverse, List.dropLast_reverse]
      intro hz
      apply hroot
      simpa using hz
    · simpa using hnil
  have hsubset := SimpleGraph.Walk.IsPath.support_subset_of_boundary_avoiding_root
    hb.reverse.dropLast hend hdrop hboundary
  intro z hz
  have hzrev : z ∈ b.reverse.dropLast.support := by
    rw [SimpleGraph.Walk.support_dropLast]
    · simp only [SimpleGraph.Walk.support_reverse, List.dropLast_reverse]
      simpa only [List.mem_reverse] using hz
    · simpa using hnil
  exact hsubset z hzrev

end Erdos64
