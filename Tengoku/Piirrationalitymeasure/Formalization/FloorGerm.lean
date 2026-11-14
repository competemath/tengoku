import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact eventual floor values of a quadratic perturbation from the right. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

def quadraticPerturbationNegative (l q : ℝ) : Prop := l < 0 ∨ (l = 0 ∧ q < 0)

noncomputable def quadraticFloorGerm (x l q : ℝ) : ℤ := by
  classical
  exact if x = (⌊x⌋ : ℝ) ∧ quadraticPerturbationNegative l q then ⌊x⌋ - 1 else ⌊x⌋

theorem quadratic_perturbation_eventually_neg {l q : ℝ}
    (hneg : quadraticPerturbationNegative l q) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, s * l + s ^ 2 * q < 0 := by
  rcases hneg with hl | ⟨rfl, hq⟩
  · have hc : ContinuousAt (fun s : ℝ => l + s * q) 0 := by fun_prop
    have he := hc.eventually_lt_const (by simpa using hl : l + 0 * q < 0)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0
    have h := mul_neg_of_pos_of_neg hs0 hs
    nlinarith only [h]
  · filter_upwards [self_mem_nhdsWithin] with s hs0
    simpa only [mul_zero, zero_add] using mul_neg_of_pos_of_neg (sq_pos_of_pos hs0) hq

theorem quadratic_perturbation_eventually_nonneg {l q : ℝ}
    (hneg : ¬quadraticPerturbationNegative l q) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, 0 ≤ s * l + s ^ 2 * q := by
  have hl0 : 0 ≤ l := le_of_not_gt (fun hl => hneg (Or.inl hl))
  by_cases hl : l = 0
  · have hq : 0 ≤ q := le_of_not_gt (fun hq => hneg (Or.inr ⟨hl, hq⟩))
    exact Eventually.of_forall fun s => by rw [hl, mul_zero, zero_add]; positivity
  · have hlpos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hl)
    have hc : ContinuousAt (fun s : ℝ => l + s * q) 0 := by fun_prop
    have he := hc.eventually_const_lt (by simpa using hlpos : 0 < l + 0 * q)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0
    have h := mul_pos hs0 hs
    nlinarith only [h]

theorem floor_quadratic_eventually (x l q : ℝ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ⌊x + s * l + s ^ 2 * q⌋ = quadraticFloorGerm x l q := by
  have hc : ContinuousAt (fun s : ℝ => x + s * l + s ^ 2 * q) 0 := by fun_prop
  have hupper := hc.eventually_lt_const
    (show x + 0 * l + 0 ^ 2 * q < (⌊x⌋ : ℝ) + 1 by simpa using Int.lt_floor_add_one x)
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have hlower := hc.eventually_const_lt
      (show (⌊x⌋ : ℝ) - 1 < x + 0 * l + 0 ^ 2 * q by simp only [zero_mul, zero_pow, zero_add, add_zero]; linarith)
    by_cases hneg : quadraticPerturbationNegative l q
    · filter_upwards [hlower.filter_mono nhdsWithin_le_nhds,
        quadratic_perturbation_eventually_neg hneg] with s hs hsneg
      rw [quadraticFloorGerm, ite_eq_left ⟨hx, hneg⟩]
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    · filter_upwards [hupper.filter_mono nhdsWithin_le_nhds,
        quadratic_perturbation_eventually_nonneg hneg] with s hs hspos
      rw [quadraticFloorGerm, ite_eq_right (fun h => hneg h.2)]
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith
  · have hlower := hc.eventually_const_lt
      (show (⌊x⌋ : ℝ) < x + 0 * l + 0 ^ 2 * q by
        simpa using (Int.floor_le x).lt_of_ne (Ne.symm hx))
    filter_upwards [hlower.filter_mono nhdsWithin_le_nhds,
      hupper.filter_mono nhdsWithin_le_nhds] with s hslo hshi
    rw [quadraticFloorGerm, ite_eq_right (fun h => hx h.1)]
    exact Int.floor_eq_iff.mpr ⟨hslo.le, hshi⟩

end PiIrrationality
