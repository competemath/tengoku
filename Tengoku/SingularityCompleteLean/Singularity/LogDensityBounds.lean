import Tengoku.Seed.MeasureTheory.Measure.Decomposition.RadonNikodym
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic bounds from measure domination

Two-sided exponential comparison of measures gives the corresponding bound
on the logarithm of their actual Radon–Nikodym derivative.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace Singularity

/-- Domination by a scalar multiple gives the almost-everywhere real density bound.
@isnad1 id=eventual.2h4v.s6.b8f0373fdeba from=translated src=- shape=65b03134 vocab=c982e732
-/
theorem real_rnDeriv_le_of_le_smul {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (C : ℝ) (hC : 0 ≤ C)
    (hdom : ν ≤ ENNReal.ofReal C • m) :
    ∀ᵐ x ∂m, (ν.rnDeriv m x).toReal ≤ C := by
  have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν m)
    (g := fun _ : X => ENNReal.ofReal C) (fun S hS _ => by
      calc
        ∫⁻ x in S, ν.rnDeriv m x ∂m ≤ ν S := Measure.setLIntegral_rnDeriv_le S
        _ ≤ (ENNReal.ofReal C • m) S := hdom S
        _ = ∫⁻ x in S, ENNReal.ofReal C ∂m := by simp)
  filter_upwards [h] with x hx
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hx

/-- Reverse domination gives the lower density bound when the measure is
absolutely continuous; finiteness of the derivative is handled almost everywhere.
@isnad1 id=eventual.3h4v.s6.8a2ddd5a3c56 from=translated src=- shape=48d04f63 vocab=63fa7afc
-/
theorem real_rnDeriv_ge_of_smul_le {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    (c : ℝ) (hc : 0 ≤ c) (hdom : ENNReal.ofReal c • m ≤ ν) :
    ∀ᵐ x ∂m, c ≤ (ν.rnDeriv m x).toReal := by
  have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (measurable_const : Measurable (fun _ : X => ENNReal.ofReal c))
    (g := ν.rnDeriv m) (fun S hS _ => by
      calc
        ∫⁻ x in S, ENNReal.ofReal c ∂m = (ENNReal.ofReal c • m) S := by simp
        _ ≤ ν S := hdom S
        _ = ∫⁻ x in S, ν.rnDeriv m x ∂m := (Measure.setLIntegral_rnDeriv hac S).symm)
  filter_upwards [h, Measure.rnDeriv_lt_top ν m] with x hx hf
  simpa only [ENNReal.toReal_ofReal hc] using ENNReal.toReal_mono hf.ne hx

/-- Exponential measure comparison becomes an absolute bound on the log density.
@isnad1 id=eventual.2h4v.s7.b8c21d107366 from=translated src=- shape=78f4b5c4 vocab=36f681d2
-/
theorem log_rnDeriv_abs_le_of_exp_comparison {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (D : ℝ)
    (hlower : ENNReal.ofReal (Real.exp (-D)) • m ≤ ν)
    (hupper : ν ≤ ENNReal.ofReal (Real.exp D) • m) :
    ∀ᵐ x ∂m, |Real.log ((ν.rnDeriv m x).toReal)| ≤ D := by
  have hac := Measure.absolutelyContinuous_of_le_smul hupper
  filter_upwards [real_rnDeriv_ge_of_smul_le ν m hac _ (Real.exp_nonneg _) hlower,
    real_rnDeriv_le_of_le_smul ν m _ (Real.exp_nonneg _) hupper] with x hl hu
  have hl' := Real.log_le_log (Real.exp_pos _) hl
  have hu' := Real.log_le_log ((Real.exp_pos _).trans_le hl) hu
  rw [Real.log_exp] at hl' hu'
  exact abs_le.mpr ⟨hl', hu'⟩

end Singularity
