/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.Topology.NoetherianSpace
import Tengoku.Seed.Topology.Connected.LocallyConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Noetherian spaces are locally connected

Connected components of a noetherian topological space are open: the complement of the
component of `x` is the union of the finitely many irreducible components not contained in
it, and irreducible components are closed. Consequently a noetherian space is locally
connected (connected components of open subsets are open, since opens of noetherian spaces
are noetherian).

Both facts appear to be missing from mathlib (2026-07-07); upstream candidates. Supply for
the componentwise canonicity glue (T-W7.7·C4glue): a locally noetherian scheme is locally
connected, so its connected components are clopen.

AINTLIB ModularCurves (T-W7.7 rigidity infrastructure); upstream candidate.
-/

open TopologicalSpace Set

variable {α : Type*} [TopologicalSpace α]

/-- In a noetherian space, connected components are open: the complement of the component of
`x` is the finite closed union of the irreducible components not contained in it.
@isnad1 id=isopen.0h2v.s4.dda7f991b8b0 from=translated src=- shape=2669ccc1 vocab=9a12ad69
-/
theorem TopologicalSpace.NoetherianSpace.isOpen_connectedComponent [NoetherianSpace α]
    (x : α) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : connectedComponent x
      = (⋃ C ∈ {C ∈ irreducibleComponents α | ¬ C ⊆ connectedComponent x}, C)ᶜ := by
    apply Set.eq_of_subset_of_subset
    · intro y hy
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
      rintro C ⟨hCmem, hCnot⟩ hyC
      refine hCnot ?_
      have hsub : C ⊆ connectedComponent y :=
        hCmem.1.2.isPreconnected.subset_connectedComponent hyC
      exact hsub.trans (connectedComponent_eq hy).ge
    · intro y hy
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hy
      by_contra hyx
      refine hy (irreducibleComponent y)
        ⟨irreducibleComponent_mem_irreducibleComponents y, fun hsub => hyx ?_⟩
        mem_irreducibleComponent
      exact hsub mem_irreducibleComponent
  rw [hcompl, isOpen_compl_iff]
  exact (hfin.subset (fun C hC => hC.1)).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)
