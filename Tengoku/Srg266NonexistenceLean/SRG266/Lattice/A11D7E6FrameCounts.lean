/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11FirstMomentCounts
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6RootPlacement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

/--
@isnad1 id=mem.1h1v.s8.cd58fffb1e72 from=translated src=- shape=88975b76 vocab=7c5428e5
-/
theorem a11D7E6A11Part_mem_integer {q : Fin 24 → ℚ}
    (hq : q ∈ coordinateIntegerLattice 24) :
    a11D7E6A11Part q ∈ coordinateIntegerLattice 11 := by
  obtain ⟨z, rfl⟩ := hq
  exact ⟨a11D7E6A11Part z, rfl⟩

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

/--
@isnad1 id=and.3h5v.s10.d87f50bcd42c from=translated src=- shape=fb813b66 vocab=ef8fd888
-/
theorem normalized_frame_counts_energy {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (δ : ℤ) (u : ι → (Fin 11 → ℚ)) (v : ι → (Fin 6 → ℚ))
    (htype : ∀ i, A11E6NormalizedType (a i) δ (u i) (v i))
    (hA : (Finset.univ.filter (fun i => a i = 9)).card = 55)
    (hB : (Finset.univ.filter (fun i => a i = 1)).card = 165) :
    (Finset.univ.filter (fun i => v i = 0)).card = 55 ∧
      (Finset.univ.filter (fun i => v i ≠ 0)).card = 165 ∧
      (∑ i, cartanARatForm 11 (u i) (u i)) = 275 ∧ (∑ i, E6Cartan.form (v i) (v i)) = 220 := by
  have hzero (i : ι) : (a i = 9 ↔ v i = 0) ∧ (a i = 1 ↔ v i ≠ 0) := by
    rcases htype i with ⟨ha, _, hv⟩ | ⟨ha, _, hn, _⟩
    · simp [ha, hv]
    · have hv : v i ≠ 0 := by
        intro h
        rw [h, map_zero] at hn
        norm_num at hn
      simp [ha, hv]
  have hnot (i : ι) : (¬a i = 9) ↔ a i = 1 := by
    rw [(hzero i).1, (hzero i).2]
  have hnormA (i : ι) : cartanARatForm 11 (u i) (u i) =
      if a i = 9 then 9/4 else 11/12 := by
    rcases htype i with ⟨ha, hn, _⟩ | ⟨ha, hn, _⟩ <;> simpa [ha] using hn
  have hnormE (i : ι) : E6Cartan.form (v i) (v i) =
      if a i = 9 then 0 else 4/3 := by
    rcases htype i with ⟨ha, _, hv⟩ | ⟨ha, _, hn, _⟩
    · simp [ha, hv]
    · simpa [ha] using hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [funext (fun i => propext (hzero i).1)] using hA
  · simpa only [funext (fun i => propext (hzero i).2)] using hB
  · simp only [hnormA, Finset.sum_ite, hnot, Finset.sum_const, nsmul_eq_mul, hA, hB]
    norm_num
  · simp only [hnormE, Finset.sum_ite, hnot, Finset.sum_const, nsmul_eq_mul, hA, hB]
    norm_num

end SRG266.Lattice
