/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEDominantBlocks
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoADEDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

theorem coordinateRootMap_pos_of_nonneg
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (coord : Fin m ≃ simpleRootSet f)
    (z : Fin m → ℤ) (hz : ∀ i, 0 ≤ z i) (hz0 : z ≠ 0) :
    0 < f (coordinateRootMap coord z) := by
  have hfpos (i : Fin m) : 0 < f (normTwoRootVal (coord i).1) :=
    IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f (coord i).2
  obtain ⟨i, hi⟩ : ∃ i, 0 < z i := by
    by_contra h
    simp only [not_exists, not_lt] at h
    apply hz0
    funext i
    exact le_antisymm (h i) (hz i)
  change 0 < toZLinearMap f (coordinateRootMap coord z)
  simp only [coordinateRootMap, Fintype.linearCombination_apply, map_sum,
    map_smul, smul_eq_mul, toZLinearMap_apply]
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hz j) (hfpos j).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (hfpos i)⟩

theorem dominant_vector_height_eq_of_coordinates
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ i j, graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) = A i j)
    (h : ℤ)
    (hheight : ∀ (θ : NormTwoRoot L) (z : Fin m → ℤ),
      coordinateRootMap coord z = θ.1 → 0 < f θ.1 →
      (∀ i, 0 ≤ L.pairing (coord i).1.1 θ.1) → (∑ i, z i) = h)
    {k : ℤ} (hv : HasDominantVector A k) : k = h := by
  obtain ⟨z, hz, hn, hd, hs⟩ := hv
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hn
  let θ : NormTwoRoot L :=
    ⟨coordinateRootMap coord z, (coordinateRootMap_pairing hf coord A hA z z).trans hn⟩
  have hθ : 0 < f θ.1 := coordinateRootMap_pos_of_nonneg coord z hz hz0
  have hdom (i : Fin m) : 0 ≤ L.pairing (coord i).1.1 θ.1 := by
    have hij (j : Fin m) : L.pairing (coord i).1.1 (coord j).1.1 = A i j :=
      (graphCartanMatrix_simpleRootGraph f hf (coord i) (coord j)).symm.trans (hA i j)
    change 0 ≤ L.pairing (coord i).1.1 (coordinateRootMap coord z)
    simp only [coordinateRootMap, Fintype.linearCombination_apply, map_sum,
      map_smul, smul_eq_mul, normTwoRootVal]
    simp_rw [hij]
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using hd i
  exact hs.symm.trans (hheight θ z rfl hθ hdom)

theorem ade_component_dominantHeight_eq
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    {ts : List ADEType} (hregular : ∀ t ∈ ts, t.IsRegular)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j, graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
      (adeGram ts).2 i j)
    (h : ℤ)
    (hheight : ∀ (θ : NormTwoRoot L) (z : Fin (ADEType.rankSum ts) → ℤ),
      coordinateRootMap coord z = θ.1 → 0 < f θ.1 →
      (∀ i, 0 ≤ L.pairing (coord i).1.1 θ.1) → (∑ i, z i) = h) :
    ∀ t ∈ ts, t.dominantHeight = h := by
  intro t ht
  exact dominant_vector_height_eq_of_coordinates hf coord (adeGram ts).2 hgram
    h hheight (adeGram_hasDominantVector_of_mem ht (hregular t ht))

end SRG266.Lattice
