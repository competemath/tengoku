import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Telescopes

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma shannonEntropy_finite {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (π : Measure W) [IsProbabilityMeasure π] :
    shannonEntropy π ≠ ∞ := by
  rw [shannonEntropy,lintegral_fintype]
  apply ENNReal.sum_ne_top.mpr
  intro w hw
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top π _)

lemma hybrid_block_numeric {d m : ℕ} {B C : ℝ}
    (hd : 256 ≤ d) (hm : m ≤ d/8) (hB : 0 ≤ B) (hBd : B ≤ (d:ℝ)^2)
    (hC : 0 ≤ C) :
    C*m+(m:ℝ)/hybridCount d*(C+B/(d/8:ℕ))+B/(d/32:ℕ) ≤ (100*C+100)*d := by
  have hh0 : (0:ℝ)<(d/8:ℕ) := by exact_mod_cast (show 0<d/8 by omega)
  have hq0 : (0:ℝ)<(d/32:ℕ) := by exact_mod_cast (show 0<d/32 by omega)
  have hN0 : (0:ℝ)<hybridCount d := by unfold hybridCount; positivity
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hmd : (m:ℝ) ≤ d := by exact_mod_cast (show m≤d by omega)
  have hdh : (d:ℝ) ≤ 16*(d/8:ℕ) := by exact_mod_cast (show d≤16*(d/8) by omega)
  have hdq : (d:ℝ) ≤ 64*(d/32:ℕ) := by exact_mod_cast (show d≤64*(d/32) by omega)
  have hmN : (m:ℝ) ≤ hybridCount d := by
    exact_mod_cast (show m≤hybridCount d by unfold hybridCount hybridFirst hybridLast; omega)
  have hmN' : (m:ℝ)/hybridCount d ≤ 1 := (div_le_one hN0).mpr hmN
  have hBh : B/(d/8:ℕ) ≤ 16*d := by
    apply (div_le_iff₀ hh0).mpr
    nlinarith
  have hBq : B/(d/32:ℕ) ≤ 64*d := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith
  have hmul : (m:ℝ)/hybridCount d*(C+B/(d/8:ℕ)) ≤ C+16*d := by
    calc
      _ ≤ 1*(C+B/(d/8:ℕ)) := mul_le_mul_of_nonneg_right hmN' (add_nonneg hC (div_nonneg hB hh0.le))
      _ ≤ C+16*d := by linarith
  have hCm := mul_le_mul_of_nonneg_left hmd hC
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  nlinarith

end CurrentProjection

end

end OAI
