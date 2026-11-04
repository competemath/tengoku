import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.RepeatedFourVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The entropy-compensated repeated-pair variation with one other atom. -/
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology

def repeatedPairBase (q z : ℝ) : Fin 3 → ℝ := ![q, q, z]
def repeatedPairPath (q z c ε : ℝ) (i : Fin 3) : ℝ :=
  quadraticPath (repeatedPairBase q z i) (![1, -1, 0] i) (![c, c, -2 * c] i) ε

@[simp] theorem repeatedPairPath_zero (q z c : ℝ) : repeatedPairPath q z c 0 = repeatedPairBase q z := by
  ext i
  simp [repeatedPairPath]

theorem repeatedPairPath_sum (q z c ε : ℝ) :
    ∑ i, repeatedPairPath q z c ε i = ∑ i, repeatedPairBase q z i := by
  simp [repeatedPairPath, repeatedPairBase, quadraticPath, Fin.sum_univ_succ]
  ring

theorem continuous_repeatedPairPath (q z c : ℝ) : Continuous (repeatedPairPath q z c) := by
  apply continuous_pi
  intro i
  unfold repeatedPairPath quadraticPath
  fun_prop

theorem repeatedPairPath_eventually_nonneg {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (c : ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, 0 ≤ repeatedPairPath q z c ε i := by
  apply eventually_all.mpr
  intro i
  have hpos : 0 < repeatedPairPath q z c 0 i := by
    rw [repeatedPairPath_zero]
    fin_cases i <;> simp [repeatedPairBase] <;> assumption
  exact (((continuous_apply i).comp (continuous_repeatedPairPath q z c)).continuousAt.eventually
    (Ioi_mem_nhds hpos)).mono (fun _ h => h.le)

theorem repeatedPairBase_pos {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (i : Fin 3) :
    0 < repeatedPairBase q z i := by fin_cases i <;> simp [repeatedPairBase] <;> assumption

namespace ProbabilityVector

end ProbabilityVector
end
end EntropyConstrainedMissingMass
