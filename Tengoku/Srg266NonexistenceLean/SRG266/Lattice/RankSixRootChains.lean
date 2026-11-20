/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RankSixComplements
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexRootChain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

/--
@isnad1 id=ex.1h1v.s8.18b498b4d6a6 from=translated src=- shape=961233f0 vocab=e52734c6
-/
theorem rankSix_has_large_A_chain (k : RankSixKind) (hk : k ≠ .seventyFive) :
    ∃ n : ℕ, (n = 0 ∨ n = 1) ∧ ∃ r : Fin (4+n) → rankSixSpace k,
      (∀ i, r i ∈ rankSixBase k) ∧
      (∀ i j, rankSixForm k (r i) (r j) = (gramA (4+n) i j : ℚ)) := by
  cases k
  · refine ⟨1, Or.inr rfl, fun i => ((simplexSimpleRoot 5 i, 0), 0), ?_, ?_⟩
    · intro i
      exact ⟨Submodule.mem_sup_left ⟨simplexSimpleRoot_mem 5 i,
        (coordinateIntegerLattice 1).zero_mem⟩, (coordinateIntegerLattice 0).zero_mem⟩
    · intro i j
      simpa only [rankSixForm, mixedPrimaryForm, primaryModelForm, E6Coordinates.form,
        prodForm_apply, map_zero, LinearMap.zero_apply, add_zero] using simplexSimpleRoot_gram 5 i j
  · refine ⟨1, Or.inr rfl, fun i => (simplexSimpleRoot 5 i, 0), ?_, ?_⟩
    · intro i
      exact Submodule.mem_sup_left ⟨simplexSimpleRoot_mem 5 i,
        (coordinateIntegerLattice 1).zero_mem⟩
    · intro i j
      simpa only [rankSixForm, H6Coordinates.form, prodForm_apply, map_zero,
        LinearMap.zero_apply, add_zero] using simplexSimpleRoot_gram 5 i j
  · refine ⟨0, Or.inl rfl, fun i => (0, simplexSimpleRoot 4 i), ?_, ?_⟩
    · intro i
      exact ⟨(coordinateIntegerLattice 2).zero_mem, simplexSimpleRoot_mem 4 i⟩
    · intro i j
      simpa only [rankSixForm, mixedPrimaryForm, primaryModelForm, prodForm_apply,
        map_zero, LinearMap.zero_apply, zero_add] using simplexSimpleRoot_gram 4 i j
  · exact (hk rfl).elim

end SRG266.Lattice
