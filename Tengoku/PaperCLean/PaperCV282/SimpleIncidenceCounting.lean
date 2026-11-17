import Tengoku.PaperCLean.PaperCV282.SimpleIncidenceModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Incidence counts in the actual connected components

In an unpinned component each incidence has a distinct other endpoint in its
row. The hypothesis of no repeated pair makes this assignment injective,
so column weights are bounded by component size minus one.
-/
namespace PaperC.V282.SimpleIncidenceCounting

open Matrix Finset SimpleGraph PinnedGraphResolution SimpleIncidenceModel

noncomputable section

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-- Incidences are allocated by their actual column component.-/
def componentMass (H : Matrix R V F₂) (c : (incidenceGraph H).ConnectedComponent) : ℕ :=
  ∑ v : c.supp, (columnSupport H v.val).card

/-- Summing over all components recovers every incidence exactly once.
@isnad1 id=eq.0h3v.s6.c3aa8361ae23 from=translated src=- shape=c188fa6e vocab=97623b45
-/
theorem sum_componentMass (H : Matrix R V F₂) :
    (∑ c : (incidenceGraph H).ConnectedComponent, componentMass H c) = incidenceMass H := by
  classical
  rw [incidenceMass_eq_sum_columnSupport]
  unfold componentMass
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (componentSupportSigmaEquiv (incidenceGraph H)) _ _ (fun _ => rfl)

/-- The degree hypothesis applies directly to each component.
@isnad1 id=le.1h5v.s6.aa122d972a6a from=translated src=- shape=f27a7e31 vocab=5d08560c
-/
theorem componentMass_le_degree (H : Matrix R V F₂) (K : ℕ)
    (hcol : ∀ v, (columnSupport H v).card ≤ K)
    (c : (incidenceGraph H).ConnectedComponent) :
    componentMass H c ≤ K * Fintype.card c.supp := by
  unfold componentMass
  calc
    _ ≤ ∑ _v : c.supp, K := Finset.sum_le_sum (fun v _ => hcol v.val)
    _ = _ := by simp [Nat.mul_comm]

/-- Every incidence at an unpinned vertex belongs to a genuine two-column row.
@isnad1 id=ex.3h5v.s6.9aae82bf96e0 from=translated src=- shape=d24446a2 vocab=15fe4cf4
-/
theorem exists_other_endpoint (H : Matrix R V F₂)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2) (v : V)
    (hpin : v ∉ pinnedColumns H) (r : R) (hr : r ∈ columnSupport H v) :
    ∃ w, w ≠ v ∧ rowSupport H r = {v,w} := by
  have hv : v ∈ rowSupport H r := (mem_rowSupport H r v).mpr ((mem_columnSupport H r v).mp hr)
  rcases row_shapes H r (hrow r) with hz | ⟨u,hu⟩ | ⟨u,w,huwn,huvw⟩
  · simp [hz] at hv
  · have he : v = u := by simpa only [hu, Finset.mem_singleton] using hv
    subst u
    exact (hpin ((mem_pinnedColumns H v).mpr ⟨r,hu⟩)).elim
  · have he : v = u ∨ v = w := by simpa only [huvw, Finset.mem_insert, Finset.mem_singleton] using hv
    rcases he with he | he
    · subst u
      exact ⟨w,huwn.symm,huvw⟩
    · subst w
      exact ⟨u,huwn,huvw.trans (Finset.pair_comm _ _)⟩

/-- Simplicity injects the row incidences into the other vertices of the component.
@isnad1 id=le.4h5v.s7.9be42f34291d from=translated src=- shape=73d06515 vocab=9b539a1c
-/
theorem columnSupport_le_component_sub_one (H : Matrix R V F₂)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s)
    (c : (incidenceGraph H).ConnectedComponent)
    (hc : ¬ ComponentPinned (incidenceGraph H) (pinnedColumns H) c)
    (v : V) (hv : v ∈ c.supp) :
    (columnSupport H v).card ≤ Fintype.card c.supp - 1 := by
  classical
  have hpin : v ∉ pinnedColumns H := by
    intro hp
    exact hc ⟨v,hp,(ConnectedComponent.mem_supp_iff c v).mp hv⟩
  let other (r : {r // r ∈ columnSupport H v}) : V :=
    (exists_other_endpoint H hrow v hpin r.val r.property).choose
  have hother (r : {r // r ∈ columnSupport H v}) :
      other r ≠ v ∧ rowSupport H r.val = {v,other r} :=
    (exists_other_endpoint H hrow v hpin r.val r.property).choose_spec
  let root : c.supp := ⟨v,hv⟩
  let f : {r // r ∈ columnSupport H v} → {w : c.supp // w ≠ root} := fun r =>
    ⟨⟨other r, c.mem_supp_of_adj_mem_supp hv ⟨(hother r).1.symm,r.val,(hother r).2⟩⟩,
      fun h => (hother r).1 (congrArg Subtype.val h)⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have he : other r = other s := congrArg (fun w : {w : c.supp // w ≠ root} => w.val.val) hrs
    apply Subtype.ext
    apply hsimple r.val s.val
    · rw [(hother r).2, Finset.card_pair (hother r).1.symm]
    · rw [(hother r).2, (hother s).2, he]
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_unique] using hcard

/-- A simple unpinned component has at most r(r−1) incidences.
@isnad1 id=le.3h4v.s7.024507d3af66 from=translated src=- shape=920ba8af vocab=59abb247
-/
theorem componentMass_le_simple (H : Matrix R V F₂)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s)
    (c : (incidenceGraph H).ConnectedComponent)
    (hc : ¬ ComponentPinned (incidenceGraph H) (pinnedColumns H) c) :
    componentMass H c ≤ Fintype.card c.supp * (Fintype.card c.supp - 1) := by
  unfold componentMass
  calc
    _ ≤ ∑ _v : c.supp, (Fintype.card c.supp - 1) :=
      Finset.sum_le_sum (fun v _ => columnSupport_le_component_sub_one H hrow hsimple c hc v.val v.property)
    _ = _ := by simp

end
end PaperC.V282.SimpleIncidenceCounting
