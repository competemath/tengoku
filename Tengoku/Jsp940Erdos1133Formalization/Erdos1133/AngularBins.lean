import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Statement
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set
namespace Erdos1133

def binCount (D L : ℝ) : ℕ := ⌊D / L⌋₊ + 1

theorem binCount_le {D L : ℝ} (hD : 0 ≤ D) (hL : 0 < L) :
    (binCount D L : ℝ) ≤ D / L + 1 := by
  simp only [binCount, Nat.cast_add, Nat.cast_one]
  simpa only [add_comm] using add_le_add_right (Nat.floor_le (div_nonneg hD hL.le)) 1

def angularBin {D L : ℝ} (hL : 0 < L) (t : Icc 0 D) : Fin (binCount D L) :=
  ⟨⌊(t : ℝ) / L⌋₊, Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right t.property.2 hL.le))⟩

theorem angularBin_bounds {D L : ℝ} (hL : 0 < L) (t : Icc 0 D) :
    (t : ℝ) ∈ Icc ((angularBin hL t).val * L) (((angularBin hL t).val + 1) * L) := by
  have ht0 : 0 ≤ (t : ℝ) / L := div_nonneg t.property.1 hL.le
  constructor
  · apply (le_div_iff₀ hL).mp
    exact Nat.floor_le ht0
  · apply le_of_lt
    apply (div_lt_iff₀ hL).mp
    exact Nat.lt_floor_add_one _

end Erdos1133
