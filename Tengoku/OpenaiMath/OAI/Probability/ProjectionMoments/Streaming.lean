import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.StoppingKernel

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
namespace Learner
universe u

end Learner

universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

lemma terminal_eq_forced_of_index (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω)
    (x : Samples d T) {t : ℕ} (ht : (L.terminal s ω x).1 = t) :
    L.terminal s ω x = (t,L.forcedRun s ω x t) := by
  rcases L.terminal_forced_witness s ω x with ⟨t',ht',he⟩
  have h : t' = t := (congrArg Prod.fst he).symm.trans ht
  subst t'
  exact he

end Learner
end

lemma streamFactor_ofReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {J : Type*} [Fintype J] (q : ℕ) :
    streamFactor (E := E) (J := J) q = ENNReal.ofReal
      ((32768:ℝ)^Module.finrank ℝ E*(Fintype.card J:ℝ)^(1/(q:ℝ))) := by
  unfold streamFactor
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity : 0 ≤ 1/(q:ℝ)),
    ENNReal.ofReal_natCast]

lemma three_mul_four_pow_le (d : ℕ) (hd : 1 ≤ d) : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
  have hp : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) hd
  calc
    (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp) (by positivity)
    _ = 12^d := by rw [← mul_pow]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) d

namespace Learner

section
universe u

end

universe u
variable {d M T : ℕ} {Ω : Type u}

end Learner
end NoiselessRegression

end

end OAI
