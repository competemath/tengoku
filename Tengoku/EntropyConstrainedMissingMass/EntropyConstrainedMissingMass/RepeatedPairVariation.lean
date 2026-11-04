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

/--
@isnad1 id=eq.0h3v.s4.31080d862f6c from=translated src=- shape=d48cce4c vocab=67b3f4c1
-/
@[simp] theorem repeatedPairPath_zero (q z c : ℝ) : repeatedPairPath q z c 0 = repeatedPairBase q z := by
  ext i
  simp [repeatedPairPath]

/--
@isnad1 id=eq.0h4v.s6.f51b58b46fc1 from=translated src=- shape=8860d982 vocab=99415859
-/
theorem repeatedPairPath_sum (q z c ε : ℝ) :
    ∑ i, repeatedPairPath q z c ε i = ∑ i, repeatedPairBase q z i := by
  simp [repeatedPairPath, repeatedPairBase, quadraticPath, Fin.sum_univ_succ]
  ring

/--
@isnad1 id=continuo.0h3v.s5.518740917b52 from=translated src=- shape=59d0fbb8 vocab=48417add
-/
theorem continuous_repeatedPairPath (q z c : ℝ) : Continuous (repeatedPairPath q z c) := by
  apply continuous_pi
  intro i
  unfold repeatedPairPath quadraticPath
  fun_prop

/--
@isnad1 id=eventual.2h3v.s6.35af2d097bc9 from=translated src=- shape=1f9b5189 vocab=0ec3421b
-/
theorem repeatedPairPath_eventually_nonneg {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (c : ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, 0 ≤ repeatedPairPath q z c ε i := by
  apply eventually_all.mpr
  intro i
  have hpos : 0 < repeatedPairPath q z c 0 i := by
    rw [repeatedPairPath_zero]
    fin_cases i <;> simp [repeatedPairBase] <;> assumption
  exact (((continuous_apply i).comp (continuous_repeatedPairPath q z c)).continuousAt.eventually
    (Ioi_mem_nhds hpos)).mono (fun _ h => h.le)

/--
@isnad1 id=lt.2h3v.s5.bde89572bdcf from=translated src=- shape=536f6de2 vocab=b18730cb
-/
theorem repeatedPairBase_pos {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (i : Fin 3) :
    0 < repeatedPairBase q z i := by fin_cases i <;> simp [repeatedPairBase] <;> assumption

namespace ProbabilityVector

end ProbabilityVector
end
end EntropyConstrainedMissingMass
