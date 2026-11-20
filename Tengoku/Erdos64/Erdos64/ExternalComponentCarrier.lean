import Tengoku.Erdos64.Erdos64.ComponentAttachments
import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped Classical

/-- The unique-root external component gives a finite rooted carrier.
Its boundary condition makes no claim about the degree retained at the root.-/
noncomputable def RootedBranchCarrier.of_externalComponent_unique_root
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    {s : V} {C : G.Walk s s} {x r : V}
    (hx : x ∉ C.support) (hr : r ∈ C.support)
    (hroot : ∀ b, b ∈ C.support →
      ((∃ v, v ∈ externalComponent G C x hx ∧ G.Adj b v) ↔ b = r)) :
    RootedBranchCarrier G := by
  classical
  let K : Set V := externalComponent G C x hx
  refine
    { carrier := K.toFinset
      root := r
      carrier_nonempty := ?_
      root_not_mem := ?_
      boundary_root := ?_ }
  · exact ⟨x, Set.mem_toFinset.mpr (mem_externalComponent_self hx)⟩
  · intro hrK
    have hrK' : r ∈ externalComponent G C x hx := Set.mem_toFinset.mp hrK
    exact hrK'.1 hr
  · intro u hu v hv huv
    have huK : u ∈ externalComponent G C x hx := Set.mem_toFinset.mp hu
    rcases externalComponent_adj_closure hx huK huv with hvC | hvK
    · exact (hroot v hvC).mp ⟨u, huK, huv.symm⟩
    · exact (hv (Set.mem_toFinset.mpr hvK)).elim

/-- Extraction keeps the actual component and the specified root, and exposes
externality and the boundary statement on the original component set.-/
theorem externalComponent_exists_rootedBranchCarrier
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    {s : V} {C : G.Walk s s} {x r : V}
    (hx : x ∉ C.support) (hr : r ∈ C.support)
    (hroot : ∀ b, b ∈ C.support →
      ((∃ v, v ∈ externalComponent G C x hx ∧ G.Adj b v) ↔ b = r)) :
    let K : Set V := externalComponent G C x hx
    ∃ B : RootedBranchCarrier G,
      B.carrier = K.toFinset ∧ B.root = r ∧
      (∀ v, v ∈ B.carrier → v ∉ C.support) ∧
      (∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = r) := by
  classical
  let B := RootedBranchCarrier.of_externalComponent_unique_root hx hr hroot
  refine ⟨B, rfl, rfl, ?_, ?_⟩
  · intro v hv
    have hvK : v ∈ externalComponent G C x hx := Set.mem_toFinset.mp hv
    exact hvK.1
  · intro u hu v hv huv
    have huB : u ∈ B.carrier := Set.mem_toFinset.mpr hu
    have hvB : v ∉ B.carrier := by
      intro hvB
      exact hv (Set.mem_toFinset.mp hvB)
    exact B.boundary_root u huB v hvB huv

end Erdos64
