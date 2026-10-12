import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.ExplorationConnectivity

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning.History
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem observe_pattern (h : History E) (R : Finset E) {ω : E → Bool}
    (hω : ω ∈ pattern h.known h.values) :
    ω ∈ pattern (h.observe R ω).known (h.observe R ω).values := by
  intro e he
  change ω e = replace R ω h.values e
  by_cases heR : e ∈ R
  · simp only [replace,ite_eq_left heR]
  · have heK : e ∈ h.known := (Finset.mem_union.mp he).resolve_right heR
    simpa only [replace,ite_eq_right heR] using hω e heK
end InfiniteConditioning.History

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def Connected : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω,x,y => BondConnected ω x y
  | .site,ω,x,y => SiteConnected ω x y

def Cluster (m : Model) (ω : m.Config) (x : Vertex) : Set Vertex :=
  {y | m.Connected ω x y}

theorem infiniteAt_iff (m : Model) (ω : m.Config) (x : Vertex) :
    ω ∈ m.InfiniteAt x ↔ (m.Cluster ω x).Infinite := by cases m <;> rfl

theorem measurableSet_infiniteAt (m : Model) (x : Vertex) : MeasurableSet (m.InfiniteAt x) := by
  cases m
  · exact measurableSet_bondInfiniteAt x
  · exact measurableSet_siteInfiniteAt x
end Model

namespace LatticeGraph

theorem conn_global (G : LatticeGraph) (m : Model) {ω : m.Config} {x y : G.Node}
    (h : G.Conn m ω x y) : m.Connected ω x.1 y.1 := by
  cases m
  · exact G.bondConn_global h
  · exact G.siteConn_global h
end LatticeGraph

namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

def Sound (s : Exploration m r) (ω : m.Config) : Prop :=
  ∀ v ∈ s.good, ∃ y, (B r v).Contains y ∧ m.Connected ω 0 y

theorem accepted_event {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values)
    (ha : s.Accept q δ t ω) : ω ∈ t.event m := by
  have hh := (accept_current_iff hs hq ω).mp ha.1
  change s.history.freeze ω ∈ t.event m at hh
  simpa only [History.freeze,replace_eq_of_pattern hω] using hh

theorem sound_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) :
    (s.advance q δ ω).Sound ω := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · obtain ⟨y,hy,hpath⟩ := accepted_event hs hq hω ha
        exact ⟨y.1,hy,t.graph.conn_global m hpath⟩
      · exact hS v hv
    · exact hS v hv

theorem run_pattern (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values) (n : ℕ) :
    ω ∈ pattern (run q δ n s ω).history.known (run q δ n s ω).history.values := by
  induction n generalizing s with
  | zero => exact hω
  | succ n ih => exact ih (s.history.observe_pattern s.reveal hω)

theorem run_sound {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) (n : ℕ) :
    (run q δ n s ω).Sound ω := by
  induction n generalizing s with
  | zero => exact hS
  | succ n ih =>
    exact ih (valid_advance hs ω) (s.history.observe_pattern s.reveal hω)
      (sound_advance hs hω hS)

theorem good_finite_of_cluster_finite {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω)
    (hfin : (m.Cluster ω 0).Finite) : (Good q δ s ω).Finite := by
  have hf (y : Vertex) : ({v | (B r v).Contains y} : Set Point).Finite := by
    apply Set.Subsingleton.finite
    intro v hv w hw
    exact cube_unique r (B_subset_Q r v y hv) (B_subset_Q r w y hw)
  apply (hfin.biUnion (fun y _ => hf y)).subset
  intro v hv
  obtain ⟨n,hn⟩ := hv
  obtain ⟨y,hy,hc⟩ := run_sound hs hω hS n v hn
  exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hc,hy⟩⟩
end Coarse.Exploration

namespace Coarse

theorem initial_sound (m : Model) (r : ℕ) {ω : m.Config}
    (hω : ω ∈ allValue (rootBits m r) true) : (initial m r).Sound ω := by
  intro v hv
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  refine ⟨0,?_,?_⟩
  · rw [B,center_zero]
    exact Box.center_mem_cube _ _
  · cases m
    · exact Relation.ReflTransGen.refl
    · refine ⟨hω 0 ?_,Relation.ReflTransGen.refl⟩
      apply Finset.mem_union_left
      exact (Box.mem_vertices _ _).mpr (zero_in_Q r)

end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

end Coarse
end CriticalZ3

end OAI
