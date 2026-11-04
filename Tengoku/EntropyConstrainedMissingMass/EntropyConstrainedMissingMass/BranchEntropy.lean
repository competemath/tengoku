import Tengoku.Seed.Analysis.SpecialFunctions.Log.NegMulLog
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Topology.Order.IntermediateValue
import Tengoku.Seed.Algebra.Order.Floor.Semiring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Entropy branch calculus from §5.2 of the manuscript. -/

namespace EntropyConstrainedMissingMass

noncomputable section

open Set

/-- Entropy of the exceptional mass `z` and `m` equal masses `(1-z)/m`.-/
def branchEntropy (m z : ℝ) : ℝ :=
  -z * Real.log z - (1 - z) * Real.log ((1 - z) / m)

theorem branchEntropy_eq_negMulLog {m : ℝ} (hm : m ≠ 0) (z : ℝ) :
    branchEntropy m z = Real.negMulLog z + Real.negMulLog (1 - z) +
      (1 - z) * Real.log m := by
  by_cases hz : 1 - z = 0
  · simp [branchEntropy, Real.negMulLog, hz]
  · rw [branchEntropy, Real.log_div hz hm]
    simp only [Real.negMulLog]
    ring

theorem continuous_branchEntropy {m : ℝ} (hm : m ≠ 0) :
    Continuous (branchEntropy m) := by
  change Continuous (fun z => branchEntropy m z)
  simp_rw [branchEntropy_eq_negMulLog hm]
  fun_prop

@[simp] theorem branchEntropy_zero (m : ℝ) : branchEntropy m 0 = Real.log m := by
  simp [branchEntropy, Real.log_inv]

@[simp] theorem branchEntropy_one (m : ℝ) : branchEntropy m 1 = 0 := by
  simp [branchEntropy]

theorem branchEntropy_uniform {m : ℝ} (hm : 0 < m) :
    branchEntropy m (1 / (m + 1)) = Real.log (m + 1) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm1 : m + 1 ≠ 0 := by positivity
  have hq : (1 - 1 / (m + 1)) / m = 1 / (m + 1) := by field_simp; ring
  rw [branchEntropy, hq]
  simp only [one_div, Real.log_inv]
  ring

/-- The support index used for entropy-matched candidates.-/
def entropySupportIndex (h : ℝ) : ℕ := ⌊Real.exp h⌋₊

theorem entropySupportIndex_pos {h : ℝ} (hh : 0 ≤ h) : 0 < entropySupportIndex h := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_exp_iff.mpr hh

theorem entropySupportIndex_log_bounds {h : ℝ} (hh : 0 ≤ h) :
    Real.log (entropySupportIndex h : ℝ) ≤ h ∧
      h < Real.log ((entropySupportIndex h : ℝ) + 1) := by
  have hk : 0 < (entropySupportIndex h : ℝ) :=
    Nat.cast_pos.mpr (entropySupportIndex_pos hh)
  constructor
  · apply (Real.log_le_iff_le_exp hk).2
    exact Nat.floor_le (Real.exp_pos h).le
  · apply (Real.lt_log_iff_exp_lt (by positivity)).2
    exact Nat.lt_floor_add_one (Real.exp h)

/-- Away from its zero endpoint, the light branch has one strictly smaller positive mass.-/
theorem light_parameter_mass_order {m a : ℝ} (hm : 0 < m)
    (ha : a ∈ Ioo 0 (1 / (m + 1))) :
    0 < a ∧ a < (1 - a) / m := by
  refine ⟨ha.1, (lt_div_iff₀ hm).2 ?_⟩
  have hmul := (lt_div_iff₀ (by positivity : 0 < m + 1)).1 ha.2
  nlinarith

/-- On the heavy branch, every repeated mass is positive and smaller than the exceptional mass.-/
theorem heavy_parameter_mass_order {m z : ℝ} (hm : 0 < m)
    (hz : z ∈ Ioo (1 / (m + 1)) 1) :
    0 < (1 - z) / m ∧ (1 - z) / m < z := by
  refine ⟨div_pos (sub_pos.mpr hz.2) hm, (div_lt_iff₀ hm).2 ?_⟩
  have hmul := (div_lt_iff₀ (by positivity : 0 < m + 1)).1 hz.1
  nlinarith

end

end EntropyConstrainedMissingMass
