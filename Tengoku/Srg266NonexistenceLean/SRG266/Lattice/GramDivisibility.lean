/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockCoordinates
import Tengoku.Seed.Data.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

def GramDivisibilityDescent {ι : Type*} [Fintype ι]
    (p : ℤ) (A : Matrix ι ι ℤ) : Prop :=
  ∀ z : ι → ℤ, (∀ i, p ∣ (A *ᵥ z) i) → ∀ i, p ∣ z i

/--
@isnad1 id=gramdivi.2h6v.s6.250d95884d51 from=translated src=- shape=73f5118c vocab=20e8cf8b
-/
theorem GramDivisibilityDescent.reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ℤ} {A : Matrix ι ι ℤ} (h : GramDivisibilityDescent p A)
    (e : κ ≃ ι) {B : Matrix κ κ ℤ} (hB : ∀ i j, B i j = A (e i) (e j)) :
    GramDivisibilityDescent p B := by
  intro z hz i
  have hrow (j : κ) : (A *ᵥ (z ∘ e.symm)) (e j) = (B *ᵥ z) j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp e]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, hB]
  have hall (j : ι) : p ∣ (A *ᵥ (z ∘ e.symm)) j := by
    have hj := hz (e.symm j)
    rw [← hrow (e.symm j)] at hj
    simpa only [Equiv.apply_symm_apply] using hj
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h _ hall (e i)

/--
@isnad1 id=gramdivi.2h5v.s6.3d63b86447d1 from=translated src=- shape=7b743d65 vocab=f25e2e14
-/
theorem GramDivisibilityDescent.block
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ℤ} {A : Matrix ι ι ℤ} {B : Matrix κ κ ℤ}
    (hA : GramDivisibilityDescent p A) (hB : GramDivisibilityDescent p B) :
    GramDivisibilityDescent p (Matrix.fromBlocks A 0 0 B) := by
  intro z hz i
  cases i with
  | inl i =>
      apply hA (z ∘ Sum.inl) _ i
      intro j
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hz (Sum.inl j)
  | inr i =>
      apply hB (z ∘ Sum.inr) _ i
      intro j
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hz (Sum.inr j)

/--
@isnad1 id=gramdivi.0h0v.s4.70bee4caa60b from=translated src=- shape=b64ad16f vocab=8d0cb6f2
-/
theorem gramE6_two_divisibility : GramDivisibilityDescent 2 (gramE 6) := by
  intro z hz i
  obtain ⟨k0, h0⟩ := hz 0
  obtain ⟨k1, h1⟩ := hz 1
  obtain ⟨k2, h2⟩ := hz 2
  obtain ⟨k3, h3⟩ := hz 3
  obtain ⟨k4, h4⟩ := hz 4
  obtain ⟨k5, h5⟩ := hz 5
  norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  change -z 1 + (2 * z 2 + (-z 3 + -z 5)) = 2 * k2 at h2
  change -z 2 + (2 * z 3 + -z 4) = 2 * k3 at h3
  change -z 3 + 2 * z 4 = 2 * k4 at h4
  change -z 2 + 2 * z 5 = 2 * k5 at h5
  fin_cases i <;> dsimp only at *
  · refine ⟨z 1 - z 5 + k5 - k1, ?_⟩
    change z 0 = 2 * (z 1 - z 5 + k5 - k1)
    linear_combination -h1 + h5
  · refine ⟨z 0 - k0, ?_⟩
    change z 1 = 2 * (z 0 - k0)
    linear_combination -h0
  · refine ⟨z 5 - k5, ?_⟩
    change z 2 = 2 * (z 5 - k5)
    linear_combination -h5
  · refine ⟨z 4 - k4, ?_⟩
    change z 3 = 2 * (z 4 - k4)
    linear_combination -h4
  · refine ⟨z 3 - z 5 + k5 - k3, ?_⟩
    change z 4 = 2 * (z 3 - z 5 + k5 - k3)
    linear_combination -h3 + h5
  · refine ⟨z 2 - z 0 + k0 - z 4 + k4 - k2, ?_⟩
    change z 5 = 2 * (z 2 - z 0 + k0 - z 4 + k4 - k2)
    linear_combination -h2 + h0 + h4

/--
@isnad1 id=gramdivi.1h2v.s5.a44822e74467 from=translated src=- shape=a413ba9c vocab=14605f8d
-/
theorem adeBlock_divisibility_of_components
    (p : ℤ) (ts : List ADEType)
    (h : ∀ t ∈ ts, GramDivisibilityDescent p t.gram) :
    GramDivisibilityDescent p (adeBlockPairing ts) := by
  induction ts with
  | nil => intro z hz i; exact Empty.elim i
  | cons t ts ih =>
      have hhead := h t (by simp)
      have htail := ih (fun s hs => h s (by simp [hs]))
      have heq : adeBlockPairing (t :: ts) =
          Matrix.fromBlocks t.gram 0 0 (adeBlockPairing ts) := by
        ext i j
        cases i <;> cases j <;> rfl
      rw [heq]
      exact hhead.block htail

/--
@isnad1 id=gramdivi.1h2v.s6.854b6c683c14 from=translated src=- shape=b276988f vocab=b2e6a97e
-/
theorem adeGram_divisibility_of_components
    (p : ℤ) (ts : List ADEType)
    (h : ∀ t ∈ ts, GramDivisibilityDescent p t.gram) :
    GramDivisibilityDescent p (adeGram ts).2 :=
  (adeBlock_divisibility_of_components p ts h).reindex (finADEBlockEquiv ts)
    (adeGram_apply_eq_adeBlockPairing ts)

/--
@isnad1 id=gramdivi.1h1v.s5.8e939be44554 from=translated src=- shape=879235e0 vocab=9e6621b4
-/
theorem adeGram_two_divisibility_of_all_E6
    (ts : List ADEType) (h : ∀ t ∈ ts, t = .E6) :
    GramDivisibilityDescent 2 (adeGram ts).2 := by
  apply adeGram_divisibility_of_components
  intro t ht
  rw [h t ht]
  exact gramE6_two_divisibility

end SRG266.Lattice
