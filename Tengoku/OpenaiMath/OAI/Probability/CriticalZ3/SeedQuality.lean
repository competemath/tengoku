import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.ShellProbability

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def BasicAdj : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω => BondOpen ω
  | .site,ω => SiteOpen ω

def VertexOpen : (m : Model) → m.Config → Vertex → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x = true

def SeedReaches (m : Model) (c : Vertex) (a b : ℕ) (T : Set Vertex) : Set m.Config :=
  {ω | ∃ x ∈ cube c a, m.VertexOpen ω x ∧ ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c b) (m.BasicAdj ω)) x y}

@[simp] theorem seedReaches_bond (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    SeedReaches .bond c a b T = bondSeedReaches c a b T := by
  ext ω; simp [SeedReaches,bondSeedReaches,VertexOpen,BasicAdj]
@[simp] theorem seedReaches_site (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    SeedReaches .site c a b T = siteSeedReaches c a b T := rfl

theorem seedReaches_mono (m : Model) (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ m.SeedReaches c a b T) := by
  cases m
  · simpa only [seedReaches_bond] using bondSeedReaches_mono c a b T
  · exact siteSeedReaches_mono c a b T
end Model

namespace Box

theorem contains_cube_iff {c x : Vertex} {n : ℕ} : (cube c n).Contains x ↔ x ∈ CriticalZ3.cube c n :=
  mem_cube.symm

theorem cube_bonds_eq (c : Vertex) (r : ℕ) :
    (cube c r).bonds = internalBonds (CriticalZ3.cube c r) (cube_finite c r) := by
  ext e
  simp only [mem_bonds,mem_internalBonds,contains_cube_iff]

theorem cube_sites_eq (c : Vertex) (r : ℕ) :
    (cube c r).vertices = (cube_finite c r).toFinset := by
  ext e
  simp only [mem_vertices,Set.Finite.mem_toFinset,contains_cube_iff]
end Box

namespace Model

theorem seedReaches_determined (m : Model) (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) ((Box.cube c b).bits m)
      (fun ω => ω ∈ m.SeedReaches c a b T) := by
  intro ω ω' h
  apply propext
  cases m
  · rw [seedReaches_bond]
    apply bondSeedReaches_determined c a b T ω ω'
    simpa only [Box.bits,Box.cube_bonds_eq] using h
  · apply siteSeedReaches_determined c a b hab T ω ω'
    simpa only [Box.bits,Box.cube_sites_eq] using h
end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

theorem basicAdj_lift {B : Box} (hB : G.ContainsBox B) {ω : m.Config} {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : m.BasicAdj ω x.1 y.1) : G.Adj m ω x y := by
  cases m
  · rcases hxy with ⟨i,hi,ho⟩ | ⟨i,hi,ho⟩
    · have he : Incidence (x.1,i) x.1 y.1 := Or.inl ⟨rfl,hi⟩
      exact ⟨(x.1,i),hB.2 (incidence_internal hx hy he),he,ho⟩
    · have he : Incidence (y.1,i) x.1 y.1 := Or.inr ⟨rfl,hi⟩
      exact ⟨(y.1,i),hB.2 (incidence_internal hx hy he),he,ho⟩
  · obtain ⟨e,he⟩ := neighbor_incidence hxy.1
    exact ⟨⟨e,hB.2 (incidence_internal hx hy he),he⟩,hxy.2⟩

/-- Exact finite-graph continuation of the quarter-face seed event. -/
theorem seedReaches_conn {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hB : G.ContainsBox (Box.cube c b)) (T : Set Vertex) {ω : m.Config}
    {v : G.Node} (hv : v.1 = c)
    (hO : ω ∈ allValue ((Box.cube c a).bits m) true)
    (hE : ω ∈ m.SeedReaches c a b T) : G.Meets m ω v T := by
  obtain ⟨x,hxa,hxo,y,hy,hpath⟩ := hE
  have hxb := cube_mono c hab hxa
  have hyb : y ∈ cube c b := by
    induction hpath with
    | refl => exact hxb
    | tail _ hab _ => exact hab.2.1
  let x' : G.Node := ⟨x,G.containsBox_node hB (Box.contains_cube_iff.mpr hxb)⟩
  let y' : G.Node := ⟨y,G.containsBox_node hB (Box.contains_cube_iff.mpr hyb)⟩
  have hxy : G.Conn m ω x' y' := by
    refine (G.conn_iff m ω x' y').mpr ⟨?_,?_⟩
    · cases m <;> exact hxo
    · apply G.lift_path (r := Within (cube c b) (m.BasicAdj ω)) ?_ ?_ hpath
      · intro x y h
        exact G.containsBox_node hB (Box.contains_cube_iff.mpr h.2.1)
      · intro x y h
        exact G.basicAdj_lift m hB (Box.contains_cube_iff.mpr h.1)
          (Box.contains_cube_iff.mpr h.2.1) h.2.2
  have hA : G.ContainsBox (Box.cube c a) := hB.mono G (fun _ h =>
    Box.contains_cube_iff.mpr (cube_mono c hab (Box.contains_cube_iff.mp h)))
  refine ⟨y',hy,G.conn_trans m ?_ hxy⟩
  apply G.open_box_conn m hA hO
  · rw [hv]; exact Box.center_mem_cube _ _
  · exact Box.contains_cube_iff.mpr hxa

end LatticeGraph
end CriticalZ3

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

theorem successBits_contained (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    C.successBits r m y ⊆ (C.expand 1).bits m := by
  have hs := bits_mono m (fun x hx => C.contains_expand 1 (C.seedBox_contained r hw y x hx))
  cases m
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact LatticeGraph.incidence_internal (exterior_expand hy)
        (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
    · exact hs he
  · exact hs
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

noncomputable def relayNode (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox C) (y : Vertex) : G.Node :=
  ⟨C.relayCenter r y,G.containsBox_node hC
    (C.seedBox_contained r hw y _ (Box.center_mem_cube _ _))⟩

theorem measurableSet_meets_goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) (τ : ℝ) :
    MeasurableSet {ω | G.Meets m ω o (G.goodRelays m p J T τ ω)} := by
  refine ProductCylinder.measurableSet_determined (G.bits m ∪ J) _ ?_
  intro ω ω' h
  have hg := G.goodRelays_determined m p J T τ ω ω' (fun e he => h e (Finset.mem_union_right _ he))
  simp only [Set.mem_ofPred_eq,hg]
  exact eq_iff_iff.mp (G.meets_determined m o _ ω ω' (fun e he => h e (Finset.mem_union_left _ he)))

end LatticeGraph
end CriticalZ3

end OAI
