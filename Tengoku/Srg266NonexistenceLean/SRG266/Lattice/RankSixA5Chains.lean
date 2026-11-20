/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RankSixRootChains

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem rankSix_has_A5_chain (k : RankSixKind) (hk : k = .ternary ∨ k = .fifteenPlus) :
    ∃ r : Fin 5 → rankSixSpace k, (∀ i, r i ∈ rankSixBase k) ∧
      (∀ i j, rankSixForm k (r i) (r j) = (gramA 5 i j : ℚ)) := by
  rcases hk with rfl | rfl
  · refine ⟨fun i => ((simplexSimpleRoot 5 i, 0), 0), ?_, ?_⟩
    · intro i
      exact ⟨Submodule.mem_sup_left ⟨simplexSimpleRoot_mem 5 i,
        (coordinateIntegerLattice 1).zero_mem⟩, (coordinateIntegerLattice 0).zero_mem⟩
    · intro i j
      simpa only [rankSixForm, mixedPrimaryForm, primaryModelForm, E6Coordinates.form,
        prodForm_apply, map_zero, LinearMap.zero_apply, add_zero] using simplexSimpleRoot_gram 5 i j
  · refine ⟨fun i => (simplexSimpleRoot 5 i, 0), ?_, ?_⟩
    · intro i
      exact Submodule.mem_sup_left ⟨simplexSimpleRoot_mem 5 i,
        (coordinateIntegerLattice 1).zero_mem⟩
    · intro i j
      simpa only [rankSixForm, H6Coordinates.form, prodForm_apply, map_zero,
        LinearMap.zero_apply, add_zero] using simplexSimpleRoot_gram 5 i j

end SRG266.Lattice
