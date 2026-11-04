import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiniteCoverPaths
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SpherePathChain
import Tengoku.Seed.Analysis.Calculus.Deriv.AffineMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Polygonal paths as actual C¹ chains, with exact length formula and
uniform piece/length bounds in a bounded finite closed convex model. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/-- Polygonal node data as the existing finite C¹-chain structure.-/
def C1ArcChain.ofNodes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (n : ℕ) (node : ℕ → E)
    (hnode : ∀ i ≤ n, node i ∈ S)
    (hseg : ∀ i < n, segment ℝ (node i) (node (i + 1)) ⊆ S) :
    C1ArcChain S (node 0) (node n) where
  pieces := n
  node := node
  curve i := AffineMap.lineMap (node i) (node (i + 1))
  velocity i _ := node (i + 1) - node i
  source := rfl
  target := rfl
  node_mem := hnode
  start := by intros; simp
  finish := by intros; simp
  derivative := fun _ _ _ _ => AffineMap.hasDerivWithinAt_lineMap
  velocity_continuous := fun _ _ => continuousOn_const
  curve_mem := fun i hi t ht => hseg i hi (lineMap_mem_segment ℝ _ _ ht)

theorem C1ArcChain.ofNodes_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (n : ℕ) (node : ℕ → E)
    (hnode : ∀ i ≤ n, node i ∈ S)
    (hseg : ∀ i < n, segment ℝ (node i) (node (i + 1)) ⊆ S) :
    (C1ArcChain.ofNodes S n node hnode hseg).length =
      ∑ i ∈ Finset.range n, dist (node i) (node (i + 1)) := by
  simp [C1ArcChain.length, C1ArcChain.ofNodes, dist_eq_norm', norm_sub_rev]

theorem C1ArcChain.ofNodes_length_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (n : ℕ) (node : ℕ → E)
    (hnode : ∀ i ≤ n, node i ∈ S)
    (hseg : ∀ i < n, segment ℝ (node i) (node (i + 1)) ⊆ S)
    (B : ℝ) (hB : ∀ i ≤ n, ‖node i‖ ≤ B) :
    (C1ArcChain.ofNodes S n node hnode hseg).length ≤ (n : ℝ) * (2 * B) := by
  rw [C1ArcChain.ofNodes_length]
  calc
    (∑ i ∈ Finset.range n, dist (node i) (node (i + 1))) ≤
        ∑ _i ∈ Finset.range n, 2 * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : i < n := Finset.mem_range.mp hi
      calc
        dist (node i) (node (i + 1)) ≤ ‖node i‖ + ‖node (i + 1)‖ := dist_le_norm_add_norm _ _
        _ ≤ B + B := add_le_add (hB i (by omega)) (hB (i + 1) (by omega))
        _ = 2 * B := by ring
    _ = _ := by simp

/-- The bounded finite convex model has actual C¹ connecting chains with
uniform piece count and length. This assertion does not concern a Hardt map.-/
theorem finite_closed_convex_cover_uniform_C1_chains
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]
    (C : ι → Set E) (hclosed : ∀ i, IsClosed (C i)) (hconvex : ∀ i, Convex ℝ (C i))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, ∀ z ∈ C i, ‖z‖ ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ x ∈ ⋃ i, C i, ∀ y ∈ connectedComponentIn (⋃ i, C i) x,
        ∃ γ : C1ArcChain (⋃ i, C i) x y, γ.pieces ≤ N ∧ γ.length ≤ L := by
  obtain ⟨N, hN, hchain⟩ := finite_closed_convex_cover_uniform_segment_chains C hclosed hconvex
  refine ⟨N, hN, max 1 ((N : ℝ) * (2 * B)), le_max_left _ _, fun x hx y hy => ?_⟩
  obtain ⟨n, hn, node, h0, hend, hseg⟩ := hchain x hx y hy
  have hsegS (i) (hi : i < n) : segment ℝ (node i) (node (i + 1)) ⊆ ⋃ j, C j := by
    obtain ⟨j, hj⟩ := hseg i hi
    exact hj.trans (subset_iUnion C j)
  have hnode (i) (hi : i ≤ n) : node i ∈ ⋃ j, C j := by
    by_cases hlt : i < n
    · exact hsegS i hlt (left_mem_segment ℝ _ _)
    · have he : i = n := by omega
      rw [he, hend]
      exact connectedComponentIn_subset _ _ hy
  have hnorm (i) (hi : i ≤ n) : ‖node i‖ ≤ B := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hnode i hi)
    exact hbound j _ hj
  let γ := C1ArcChain.ofNodes (⋃ i, C i) n node hnode hsegS
  have hlen : γ.length ≤ max 1 ((N : ℝ) * (2 * B)) := by
    apply (C1ArcChain.ofNodes_length_le _ n node hnode hsegS B hnorm).trans
    apply le_trans _ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
  have hh : ∃ δ : C1ArcChain (⋃ i, C i) (node 0) (node n),
      δ.pieces ≤ N ∧ δ.length ≤ max 1 ((N : ℝ) * (2 * B)) := ⟨γ, hn, hlen⟩
  subst x y
  exact hh

end
end DuistermaatVanDerKallen
