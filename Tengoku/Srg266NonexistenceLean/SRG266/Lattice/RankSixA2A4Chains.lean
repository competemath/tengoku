/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RankSixRootChains

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

/--
@isnad1 id=ex.0h0v.s10.9bb3bbb74ae0 from=translated src=- shape=2989e821 vocab=326a442a
-/
theorem rankSix_fifteenMinus_has_A2_A4 :
    ∃ (r : Fin 2 → rankSixSpace .fifteenMinus) (s : Fin 4 → rankSixSpace .fifteenMinus),
      (∀ i, r i ∈ rankSixBase .fifteenMinus) ∧
      (∀ j, s j ∈ rankSixBase .fifteenMinus) ∧
      (∀ i j, rankSixForm .fifteenMinus (r i) (r j) = (gramA 2 i j : ℚ)) ∧
      (∀ i j, rankSixForm .fifteenMinus (s i) (s j) = (gramA 4 i j : ℚ)) ∧
      (∀ i j, rankSixForm .fifteenMinus (r i) (s j) = 0) := by
  refine ⟨fun i => (simplexSimpleRoot 2 i, 0), fun j => (0, simplexSimpleRoot 4 j), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨simplexSimpleRoot_mem 2 i, (coordinateIntegerLattice 4).zero_mem⟩
  · intro j
    exact ⟨(coordinateIntegerLattice 2).zero_mem, simplexSimpleRoot_mem 4 j⟩
  · intro i j
    simpa only [rankSixForm, mixedPrimaryForm, primaryModelForm, prodForm_apply,
      map_zero, LinearMap.zero_apply, add_zero] using simplexSimpleRoot_gram 2 i j
  · intro i j
    simpa only [rankSixForm, mixedPrimaryForm, primaryModelForm, prodForm_apply,
      map_zero, LinearMap.zero_apply, zero_add] using simplexSimpleRoot_gram 4 i j
  · intro i j
    simp only [rankSixForm, mixedPrimaryForm, primaryModelForm, prodForm_apply,
      map_zero, LinearMap.zero_apply, add_zero]

end SRG266.Lattice
