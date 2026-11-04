import Tengoku.Seed.Analysis.Convex.Topology
import Tengoku.Seed.Analysis.Convex.PathConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite closed-cover connectivity gives finite intersection chains. For
convex cells these give polygonal paths with a uniform segment-count bound.
The cover is fixed; no semialgebraic decomposition or Hardt theorem is assumed. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

theorem finite_closed_cover_component_chain
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    {i j : ι} {x y : X} (hx : x ∈ C i) (hy : y ∈ C j)
    (hxy : y ∈ connectedComponentIn (⋃ k, C k) x) :
    Relation.ReflTransGen (fun k l => (C k ∩ C l).Nonempty) i j := by
  classical
  let R := Relation.ReflTransGen (fun k l => (C k ∩ C l).Nonempty)
  let U : Set X := ⋃ k : {k // R i k}, C k.val
  let V : Set X := ⋃ k : {k // ¬ R i k}, C k.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun k => hC k.val)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k => hC k.val)
  by_contra hnot
  have hsub : connectedComponentIn (⋃ k, C k) x ⊆ U ∪ V := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp (connectedComponentIn_subset _ _ hz)
    by_cases hr : R i k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, hr⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hr⟩, hk⟩)
  have hxin : (connectedComponentIn (⋃ k, C k) x ∩ U).Nonempty :=
    ⟨x, mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hx⟩),
      mem_iUnion.mpr ⟨⟨i, Relation.ReflTransGen.refl⟩, hx⟩⟩
  have hyin : (connectedComponentIn (⋃ k, C k) x ∩ V).Nonempty :=
    ⟨y, hxy, mem_iUnion.mpr ⟨⟨j, hnot⟩, hy⟩⟩
  obtain ⟨z, _, hzU, hzV⟩ := isPreconnected_closed_iff.mp
    isPreconnected_connectedComponentIn U V hU hV hsub hxin hyin
  obtain ⟨k, hk⟩ := mem_iUnion.mp hzU
  obtain ⟨l, hl⟩ := mem_iUnion.mp hzV
  exact l.property (k.property.tail ⟨z, hk, hl⟩)

/-- An explicit finite index sequence witnessing reflexive-transitive closure.-/
theorem exists_finite_relation_chain {ι : Type*} {R : ι → ι → Prop} {i j : ι}
    (h : Relation.ReflTransGen R i j) :
    ∃ n : ℕ, ∃ u : ℕ → ι, u 0 = i ∧ u n = j ∧ ∀ k < n, R (u k) (u (k + 1)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => j, rfl, rfl, fun _ h => by omega⟩
  | @head i k hik _ ih =>
    obtain ⟨n, u, h0, hn, hstep⟩ := ih
    refine ⟨n + 1, fun k => Nat.casesOn k i u, rfl, hn, ?_⟩
    intro k hk
    cases k with
    | zero =>
      change R i (u 0)
      rw [h0]
      exact hik
    | succ k => exact hstep k (by omega)

/-- One finite bound works for all reachable pairs in a finite model.-/
theorem uniform_finite_relation_chains {ι : Type*} [Finite ι] (R : ι → ι → Prop) :
    ∃ N : ℕ, ∀ i j, Relation.ReflTransGen R i j →
      ∃ n ≤ N, ∃ u : ℕ → ι, u 0 = i ∧ u n = j ∧ ∀ k < n, R (u k) (u (k + 1)) := by
  classical
  let P := {p : ι × ι // Relation.ReflTransGen R p.1 p.2}
  let : Fintype P := Fintype.ofFinite P
  choose n u h0 hn hstep using fun p : P => exists_finite_relation_chain p.property
  refine ⟨Finset.univ.sup n, fun i j hij => ?_⟩
  let p : P := ⟨(i, j), hij⟩
  exact ⟨n p, Finset.le_sup (f := n) (Finset.mem_univ p), u p, h0 p, hn p, hstep p⟩

/-- A chain of overlapping convex cells gives one straight segment per cell.-/
theorem convex_cover_segment_chain
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (C : ι → Set E) (hC : ∀ i, Convex ℝ (C i))
    {n : ℕ} (u : ℕ → ι)
    (hstep : ∀ k < n, (C (u k) ∩ C (u (k + 1))).Nonempty)
    {x y : E} (hx : x ∈ C (u 0)) (hy : y ∈ C (u n)) :
    ∃ node : ℕ → E, node 0 = x ∧ node (n + 1) = y ∧
      ∀ k < n + 1, ∃ i, segment ℝ (node k) (node (k + 1)) ⊆ C i := by
  induction n generalizing u x with
  | zero =>
    refine ⟨fun k => Nat.casesOn k x (fun _ => y), rfl, rfl, ?_⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact ⟨u 0, (hC (u 0)).segment_subset hx hy⟩
  | succ n ih =>
    obtain ⟨z, hz0, hz1⟩ := hstep 0 (by omega)
    obtain ⟨v, hv0, hvn, hv⟩ := ih (fun k => u (k + 1))
      (fun k hk => hstep (k + 1) (by omega)) hz1 hy
    refine ⟨fun k => Nat.casesOn k x v, rfl, hvn, ?_⟩
    intro k hk
    cases k with
    | zero =>
      change ∃ i, segment ℝ x (v 0) ⊆ C i
      rw [hv0]
      exact ⟨u 0, (hC (u 0)).segment_subset hx hz0⟩
    | succ k => exact hv k (by omega)

/-- The finite model has a uniform bound on polygonal segment count.
Every segment is contained in a single original cell.-/
theorem finite_closed_convex_cover_uniform_segment_chains
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [Finite ι]
    (C : ι → Set E) (hclosed : ∀ i, IsClosed (C i)) (hconvex : ∀ i, Convex ℝ (C i)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x ∈ ⋃ i, C i, ∀ y ∈ connectedComponentIn (⋃ i, C i) x,
      ∃ n ≤ N, ∃ node : ℕ → E, node 0 = x ∧ node n = y ∧
        ∀ k < n, ∃ i, segment ℝ (node k) (node (k + 1)) ⊆ C i := by
  obtain ⟨N, hN⟩ := uniform_finite_relation_chains (fun i j => (C i ∩ C j).Nonempty)
  refine ⟨N + 1, by omega, fun x hx y hy => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp (connectedComponentIn_subset _ _ hy)
  obtain ⟨n, hn, u, hu0, hun, hstep⟩ := hN i j
    (finite_closed_cover_component_chain C hclosed hi hj hy)
  have hxu : x ∈ C (u 0) := hu0.symm ▸ hi
  have hyu : y ∈ C (u n) := hun.symm ▸ hj
  obtain ⟨node, h0, hend, hseg⟩ := convex_cover_segment_chain C hconvex u hstep hxu hyu
  exact ⟨n + 1, by omega, node, h0, hend, hseg⟩

end
end DuistermaatVanDerKallen
