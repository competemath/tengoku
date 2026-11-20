/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEDominantVectors
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockCoordinates
import Tengoku.Seed.Data.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

theorem HasDominantVector.reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {A : Matrix ι ι ℤ} {B : Matrix κ κ ℤ} {h : ℤ}
    (hv : HasDominantVector A h) (e : κ ≃ ι)
    (hB : ∀ i j, B i j = A (e i) (e j)) : HasDominantVector B h := by
  obtain ⟨z, hz, hn, hd, hs⟩ := hv
  have hrow (i : κ) : (B *ᵥ (fun j => z (e j))) i = (A *ᵥ z) (e i) := by
    simp only [Matrix.mulVec, dotProduct, hB]
    exact Equiv.sum_comp e (fun j => A (e i) j * z j)
  refine ⟨fun i => z (e i), fun i => hz (e i), ?_, ?_, ?_⟩
  · rw [Matrix.toBilin'_apply'] at hn ⊢
    simp only [dotProduct] at hn ⊢
    simp_rw [hrow]
    exact (Equiv.sum_comp e (fun i => z i * (A *ᵥ z) i)).trans hn
  · intro i
    rw [hrow]
    exact hd (e i)
  · exact (Equiv.sum_comp e z).trans hs

theorem HasDominantVector.blockLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {A : Matrix ι ι ℤ} (B : Matrix κ κ ℤ) {h : ℤ}
    (hv : HasDominantVector A h) :
    HasDominantVector (Matrix.fromBlocks A 0 0 B) h := by
  obtain ⟨z, hz, hn, hd, hs⟩ := hv
  refine ⟨Sum.elim z (fun _ => 0), ?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hz i
    · exact le_rfl
  · simpa [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks] using hn
  · rintro (i | i)
    · simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks] using hd i
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]
  · simpa [Fintype.sum_sum_type] using hs

theorem HasDominantVector.blockRight
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℤ) {B : Matrix κ κ ℤ} {h : ℤ}
    (hv : HasDominantVector B h) :
    HasDominantVector (Matrix.fromBlocks A 0 0 B) h := by
  obtain ⟨z, hz, hn, hd, hs⟩ := hv
  refine ⟨Sum.elim (fun _ => 0) z, ?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact le_rfl
    · exact hz i
  · simpa [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks] using hn
  · rintro (i | i)
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]
    · simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks] using hd i
  · simpa [Fintype.sum_sum_type] using hs

theorem adeBlock_hasDominantVector_of_mem
    {t : ADEType} {ts : List ADEType} {h : ℤ}
    (ht : t ∈ ts) (hv : HasDominantVector t.gram h) :
    HasDominantVector (adeBlockPairing ts) h := by
  induction ts with
  | nil => simp at ht
  | cons s ts ih =>
      have hM : adeBlockPairing (s :: ts) =
          Matrix.fromBlocks s.gram 0 0 (adeBlockPairing ts) := by
        ext (i | i) (j | j) <;> rfl
      rw [hM]
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hv.blockLeft _
      · exact (ih ht).blockRight _

theorem adeGram_hasDominantVector_of_mem
    {t : ADEType} {ts : List ADEType} (ht : t ∈ ts) (hregular : t.IsRegular) :
    HasDominantVector (adeGram ts).2 t.dominantHeight :=
  (adeBlock_hasDominantVector_of_mem ht (t.hasDominantVector hregular)).reindex
    (finADEBlockEquiv ts) (adeGram_apply_eq_adeBlockPairing ts)

end SRG266.Lattice
