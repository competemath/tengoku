import Tengoku.Erdos64.Erdos64.ResidualRootExcursions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The shared-root quotient certificate composes into an explicit dichotomy:
either the residual path avoids the shared root and closes to a dyadic
port-to-port path, or it contains the root and splits into two excursions whose
fan-cycle lengths are both certified non-dyadic in a minimal counterexample.
@isnad1 id=ex.6h5v.s9.d4ae486d26b5 from=translated src=- shape=4abada26 vocab=f422646a
-/
theorem MinimalCounterexample.shared_root_residual_case_split
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {r x y : V}
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hroot_degree : 4 ≤ G.degree r) :
    ∃ k : ℕ, ∃ u v : V, ∃ p : G.Walk u v,
      k ≥ 2 ∧
      p.IsPath ∧
      (∀ w, w ∈ p.support → w ≠ x ∧ w ≠ y) ∧
      p.length + 2 = 2 ^ k ∧
      (((r ∉ p.support) ∧
          ((∃ q : G.Walk x y,
              q.IsPath ∧ r ∉ q.support ∧ q.length = 2 ^ k) ∨
            (∃ q : G.Walk y x,
              q.IsPath ∧ r ∉ q.support ∧ q.length = 2 ^ k))) ∨
        ((r ∈ p.support) ∧
          ∃ a : G.Walk u r, ∃ b : G.Walk r v,
            a.IsPath ∧ b.IsPath ∧ a.append b = p ∧
            a.support ⊆ p.support ∧ b.support ⊆ p.support ∧
            a.length + b.length = p.length ∧
            0 < a.length ∧ 0 < b.length ∧
            r ∉ a.support.dropLast ∧ r ∉ b.support.tail ∧
            (∀ j : ℕ, 2 ≤ j → a.length + 2 ≠ 2 ^ j) ∧
            (∀ j : ℕ, 2 ≤ j → b.length + 2 ≠ 2 ^ j))) := by
  obtain ⟨k, u, v, p, hk, hp, havoid, hlen, hadj⟩ :=
    M.shared_root_quotient_residual_path hrx hry hxy hnadj hroot_degree
  rcases hadj with ⟨hxu, hyv, hur, hvr⟩ | ⟨hyu, hxv, hur, hvr⟩
  · by_cases hroot : r ∈ p.support
    · refine ⟨k, u, v, p, hk, hp, havoid, hlen, Or.inr ⟨hroot, ?_⟩⟩
      exact M.cross_residual_root_internal_excursions_nondyadic
        hrx hry hp havoid hur hvr hroot (Or.inl ⟨hxu, hyv⟩)
    · refine ⟨k, u, v, p, hk, hp, havoid, hlen, Or.inl ⟨hroot, ?_⟩⟩
      exact cross_residual_path_to_dyadic_port_path
        hrx hry hxy hp havoid hroot hlen (Or.inl ⟨hxu, hyv⟩)
  · by_cases hroot : r ∈ p.support
    · refine ⟨k, u, v, p, hk, hp, havoid, hlen, Or.inr ⟨hroot, ?_⟩⟩
      exact M.cross_residual_root_internal_excursions_nondyadic
        hrx hry hp havoid hur hvr hroot (Or.inr ⟨hyu, hxv⟩)
    · refine ⟨k, u, v, p, hk, hp, havoid, hlen, Or.inl ⟨hroot, ?_⟩⟩
      exact cross_residual_path_to_dyadic_port_path
        hrx hry hxy hp havoid hroot hlen (Or.inr ⟨hyu, hxv⟩)

/-- Once both endpoints of a root-internal split lie in one closed side, the
root-free interiors of both excursions lie in that side.  This is the exact
boundary interface needed before any balanced-side forcing argument can use
the split.
@isnad1 id=and.9h8v.s7.301e92e6bd43 from=translated src=- shape=0408a684 vocab=92466c5b
-/
theorem residual_root_internal_excursion_interiors_in_closed_side
    {V : Type u} {G : SimpleGraph V}
    {D : Finset V} {r u v : V}
    {a : G.Walk u r} {b : G.Walk r v}
    (ha : a.IsPath) (hb : b.IsPath)
    (hapos : 0 < a.length) (hbpos : 0 < b.length)
    (hroota : r ∉ a.support.dropLast)
    (hrootb : r ∉ b.support.tail)
    (hu : u ∈ D) (hv : v ∈ D)
    (hboundary :
      ∀ x, x ∈ D → ∀ y, y ∉ D → G.Adj x y → y = r) :
    (∀ z, z ∈ a.support.dropLast → z ∈ D) ∧
      (∀ z, z ∈ b.support.tail → z ∈ D) := by
  constructor
  · exact Erdos64.SimpleGraph.Walk.IsPath.dropLast_support_subset_of_boundary
      ha hapos hu hroota hboundary
  · exact Erdos64.SimpleGraph.Walk.IsPath.tail_support_subset_of_boundary
      hb hbpos hv hrootb hboundary

end Erdos64
