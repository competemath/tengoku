import Tengoku.Twinprime.TwinPrime.Analytic.DyadicNatPartition
import Tengoku.Twinprime.TwinPrime.Analytic.VaughanBoxCoefficients
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterMaximalBilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Active masked Vaughan boxes

The active family retains only cells that can meet both strict lower
cutoffs and the product cutoff. Every discarded cell contributes zero,
including after taking the finite product-cutoff maximum. The family has
at most the square of the dyadic depth; its side lengths satisfy the
half-cutoff bounds needed by the polynomial estimate.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

def activeVaughanBoxes (U V T : ℕ) : Finset (ℕ × ℕ) :=
  ((range (dyadicNatDepth T)).product (range (dyadicNatDepth T))).filter fun p =>
    U < 2 ^ (p.1 + 1) ∧ V < 2 ^ (p.2 + 1) ∧ 2 ^ p.1 * 2 ^ p.2 ≤ T

theorem card_activeVaughanBoxes_le (U V T : ℕ) :
    (activeVaughanBoxes U V T).card ≤ (dyadicNatDepth T) ^ 2 := by
  exact (card_filter_le _ _).trans_eq (by simp [card_product, pow_two])

@[simp] theorem activeVaughanBoxes_zero (U V : ℕ) : activeVaughanBoxes U V 0 = ∅ := by
  simp [activeVaughanBoxes]

/-- The full set of natural inequalities retained by active membership.-/
theorem mem_activeVaughanBoxes_iff (U V T k j : ℕ) :
    (k, j) ∈ activeVaughanBoxes U V T ↔
      k < dyadicNatDepth T ∧ j < dyadicNatDepth T ∧
        U < 2 ^ (k + 1) ∧ V < 2 ^ (j + 1) ∧ 2 ^ k * 2 ^ j ≤ T := by
  simp only [activeVaughanBoxes, mem_filter, product_eq_sprod, mem_product, mem_range]
  tauto

/-- An inactive cell vanishes for every character and every cutoff at most `T`.-/
theorem vaughanBox_characterProductCutoffSum_eq_zero_of_inactive {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U V T k j t : ℕ) (ht : t ≤ T)
    (hinactive : ¬ (U < 2 ^ (k + 1) ∧ V < 2 ^ (j + 1) ∧ 2 ^ k * 2 ^ j ≤ T)) :
    characterProductCutoffSum χ (vaughanBoxA U T) (vaughanBoxB V T)
      (2 ^ k) (2 ^ j) k j t = 0 := by
  unfold characterProductCutoffSum
  apply sum_eq_zero
  intro m hm
  apply sum_eq_zero
  intro n hn
  by_cases hmU : m ≤ U
  · rw [vaughanBoxA_eq_zero_of_le U T m hmU, zero_mul, zero_mul]
  by_cases hnV : n ≤ V
  · rw [vaughanBoxB_eq_zero_of_le V T n hnV, mul_zero, zero_mul]
  have hmb := mem_Ico.mp hm
  have hnb := mem_Ico.mp (mem_filter.mp hn).1
  have hmn : m * n ≤ T := (mem_filter.mp hn).2.trans ht
  have hpowk : 2 ^ (k + 1) = (2 : ℕ) ^ k + 2 ^ k := by rw [pow_succ]; omega
  have hpowj : 2 ^ (j + 1) = (2 : ℕ) ^ j + 2 ^ j := by rw [pow_succ]; omega
  exact (hinactive ⟨by omega, by omega, (Nat.mul_le_mul hmb.1 hnb.1).trans hmn⟩).elim

/-- Inactive cells also have zero finite product-cutoff maximum.-/
theorem vaughanBox_characterProductCutoffMax_eq_zero_of_inactive {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U V T k j : ℕ)
    (hinactive : ¬ (U < 2 ^ (k + 1) ∧ V < 2 ^ (j + 1) ∧ 2 ^ k * 2 ^ j ≤ T)) :
    characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
      (2 ^ k) (2 ^ j) k j T = 0 := by
  obtain ⟨t, ht, hmax⟩ := Finset.exists_mem_eq_sup'
    (show (Icc 0 T).Nonempty from ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩)
    (fun t => ‖characterProductCutoffSum χ (vaughanBoxA U T) (vaughanBoxB V T)
      (2 ^ k) (2 ^ j) k j t‖)
  unfold characterProductCutoffMax
  rw [hmax, vaughanBox_characterProductCutoffSum_eq_zero_of_inactive
    χ U V T k j t (mem_Icc.mp ht).2 hinactive, norm_zero]

/-- A discarded box from the depth-indexed family has zero cutoff sum.-/
theorem vaughanBox_characterProductCutoffSum_eq_zero_of_not_mem {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U V T k j t : ℕ) (ht : t ≤ T)
    (hk : k < dyadicNatDepth T) (hj : j < dyadicNatDepth T)
    (hnot : (k, j) ∉ activeVaughanBoxes U V T) :
    characterProductCutoffSum χ (vaughanBoxA U T) (vaughanBoxB V T)
      (2 ^ k) (2 ^ j) k j t = 0 := by
  apply vaughanBox_characterProductCutoffSum_eq_zero_of_inactive χ U V T k j t ht
  intro h
  exact hnot ((mem_activeVaughanBoxes_iff U V T k j).mpr ⟨hk, hj, h⟩)

/-- A discarded box from the depth-indexed family has zero cutoff maximum.-/
theorem vaughanBox_characterProductCutoffMax_eq_zero_of_not_mem {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U V T k j : ℕ)
    (hk : k < dyadicNatDepth T) (hj : j < dyadicNatDepth T)
    (hnot : (k, j) ∉ activeVaughanBoxes U V T) :
    characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
      (2 ^ k) (2 ^ j) k j T = 0 := by
  apply vaughanBox_characterProductCutoffMax_eq_zero_of_inactive χ U V T k j
  intro h
  exact hnot ((mem_activeVaughanBoxes_iff U V T k j).mpr ⟨hk, hj, h⟩)

/-- The real side bounds and natural depth bounds used by the box estimate.
The factor `1/2` comes from using global power-of-two cells.-/
theorem activeVaughanBoxes_bounds (U V T k j : ℕ)
    (h : (k, j) ∈ activeVaughanBoxes U V T) :
    (U : ℝ) / 2 ≤ (2 : ℝ) ^ k ∧ (V : ℝ) / 2 ≤ (2 : ℝ) ^ j ∧
      (2 : ℝ) ^ k * 2 ^ j ≤ (T : ℝ) ∧
        k + 1 ≤ dyadicNatDepth T ∧ j + 1 ≤ dyadicNatDepth T := by
  obtain ⟨hk, hj, hU, hV, hprod⟩ := (mem_activeVaughanBoxes_iff U V T k j).mp h
  have hUr : (U : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hU
  have hVr : (V : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast hV
  rw [pow_succ] at hUr hVr
  refine ⟨by linarith, by linarith, ?_, by omega, by omega⟩
  exact_mod_cast hprod

/-- The two depth factors of every active box are at most the square of
the common dyadic depth.-/
theorem activeVaughanBoxes_depth_product_le (U V T k j : ℕ)
    (h : (k, j) ∈ activeVaughanBoxes U V T) :
    (k + 1) * (j + 1) ≤ (dyadicNatDepth T) ^ 2 := by
  have hb := activeVaughanBoxes_bounds U V T k j h
  simpa only [pow_two] using Nat.mul_le_mul hb.2.2.2.1 hb.2.2.2.2

end TwinPrime.Analytic
